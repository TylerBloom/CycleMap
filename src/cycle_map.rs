use std::{
    borrow::Borrow,
    default::Default,
    fmt::{self, Debug},
    hash::{BuildHasher, Hash},
    iter::FusedIterator,
};

use core::mem;

use hashbrown::{hash_map::DefaultHashBuilder, TryReserveError};

use crate::{
    optionals::*,
    raw_cycle_map::{RawCycleMap, RawDrainIter, RawIter, RawSingleIter, MappingItem},
};
use OptionalPair::*;

#[cfg(doc)]
use hashbrown::HashMap;

/// A hash map implementation that allows bi-directional, constant time lookups.
///
/// `CycleMap` bijectively maps two sets together. In other words, every item in a set is paired
/// with one and only one item in the other set. It does this while maintaining the same
/// complexitity for lookups as a traditional hash map and while only keeping a single copy of each
/// element.
///
/// `CycleMap` is built on top of the [`HashMap`] implementation found in [`hashbrown`].
/// As such, it uses the same default hashing algorithm as `hashbrown`'s `HashMap`.
///
/// Moreover, the requirements for a "key" for a `HashMap` is required for all values of a
/// CycleMap, namely [`Eq`] and [`Hash`].
///
/// # Examples
/// ```
/// use cycle_map::CycleMap;
///
/// let values = vec![ ("zero", 0), ("one", 1), ("two", 2), ("three", 3), ("four", 4), ("five", 5),
/// ("six", 6), ("seven", 7), ("eight", 8), ("nine", 9), ];
///
/// let mut converter: CycleMap<String, u64> = values.iter()
///                                                  .cloned()
///                                                  .map(|(s,i)| (s.to_string(),i))
///                                                  .collect();
///
/// // The map should contain 10 pairs
/// assert_eq!(converter.len(), 10);
///
/// // See if your value number is here
/// if converter.contains_right(&42) {
///     println!( "I know the answer to life!!" );
/// }
///
/// // Get a value from either side!
/// assert_eq!(converter.get_left(&7), Some(&"seven".to_string()));
/// assert_eq!(converter.get_right(&"three".to_string()), Some(&3));
///
/// // Removing an item removes the whole pair
/// assert_eq!(converter.remove_via_right(&7), Some(("seven".to_string(), 7)));
/// assert_eq!(converter.remove_via_left(&"three".to_string()), Some(("three".to_string(), 3)));
///
/// // Remove all pairs with an odd right item
/// converter.retain(|_,i| i % 2 == 0);
/// assert!(converter.contains_right(&2));
///
/// ```
pub struct CycleMap<L, R, St = DefaultHashBuilder> {
    table: RawCycleMap<L, R, St>,
}

impl<L, R> CycleMap<L, R, DefaultHashBuilder> {
    #[inline]
    /// Creates a new, empty `CycleMap`.
    /// The capacity of the new map will be 0.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    /// let map: CycleMap<u64, String> = CycleMap::new();
    /// ```
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    /// Creates a new, empty `CycleMap` with inner sets that each have at least the given capacity.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    /// let map: CycleMap<u64, String> = CycleMap::with_capacity(100);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, DefaultHashBuilder::default())
    }
}

impl<L, R, S> CycleMap<L, R, S>
where
    L: Eq + Hash + Debug,
    R: Eq + Hash + Debug,
    S: BuildHasher,
{
    /// Adds a pair of items to the map.
    ///
    /// Should the left element be equal to another left element, the pair containing the old left
    /// item is removed and returned. The same goes for the new right element.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::{CycleMap, OptionalPair::*};
    ///
    /// let mut map: CycleMap<u64, String> = (0..5).map(|i| (i, i.to_string())).collect();
    ///
    /// // Neither 5 nor "5" is in map
    /// let op = map.insert(5, 5.to_string());
    /// assert_eq!(op, Neither);
    ///
    /// // 0 is in the map, its old pairing is removed
    /// let op = map.insert(0, 6.to_string());
    /// assert_eq!(op, SomeLeft((0, 0.to_string())));
    ///
    /// // "1" is in the map, its old pairing is removed
    /// let op = map.insert(7, 1.to_string());
    /// assert_eq!(op, SomeRight((1, 1.to_string())));
    ///
    /// // Both 2 and "3" are in the map, so their old pairings are removed
    /// let op = map.insert(2, 3.to_string());
    /// assert_eq!(op, SomeBoth((2, 2.to_string()),(3, 3.to_string())));
    /// ```
    pub fn insert(&mut self, left: L, right: R) -> InsertOptional<L, R> {
        let opt_from_left = self.remove_via_left(&left);
        let opt_from_right = self.remove_via_right(&right);
        self.table.insert(left, right);
        InsertOptional::from((opt_from_left, opt_from_right))
    }

    /// Returns `true` if both items are in the map and are paired together; otherwise, returns
    /// `false`.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    ///
    /// let mut map = CycleMap::new();
    /// map.insert(1, "1");
    /// assert!(map.are_paired(&1, &"1"));
    /// assert!(!map.are_paired(&2, &"1"));
    /// assert!(!map.are_paired(&2, &"2"));
    /// ```
    pub fn are_paired(&self, left: &L, right: &R) -> bool {
        self.table.are_paired(left, right)
    }

    /// Returns `true` if the item is found and `false` otherwise.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    ///
    /// let mut map = CycleMap::new();
    /// map.insert(1, "1");
    /// assert!(map.contains_left(&1));
    /// assert!(!map.contains_left(&2));
    /// ```
    pub fn contains_left(&self, left: &L) -> bool {
        self.table.contains_left(left)
    }

    /// Returns `true` if the item is found and `false` otherwise.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    ///
    /// let mut map = CycleMap::new();
    /// map.insert(1, "1");
    /// assert!(map.contains_right(&"1"));
    /// assert!(!map.contains_right(&"2"));
    /// ```
    pub fn contains_right(&self, right: &R) -> bool {
        self.table.contains_right(right)
    }

    /// Removes and returns the give pair from the map provided that they are paired together.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    ///
    /// let mut map = CycleMap::new();
    /// map.insert(1, "1");
    /// assert_eq!(map.remove(&1, &"1"), Some((1, "1")));
    /// assert_eq!(map.remove(&1, &"1"), None);
    /// ```
    pub fn remove(&mut self, left: &L, right: &R) -> Option<(L, R)> {
        if self.are_paired(left, right) {
            self.remove_via_left(left)
        } else {
            None
        }
    }

    /// Removes and returns the given item from the left set and its associated item from the right
    /// set.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    ///
    /// let mut map = CycleMap::new();
    /// map.insert(1, "1");
    /// assert_eq!(map.remove_via_left(&1), Some((1, "1")));
    /// assert_eq!(map.remove_via_left(&1), None);
    /// ```
    pub fn remove_via_left(&mut self, item: &L) -> Option<(L, R)> {
        // This order of these operations matter
        // `remove_via_left` gets a left pairing to get a right pairing
        let right = self.table.remove_via_left(item)?;
        let left = self.table.remove_left(item).unwrap();
        Some((left.extract(), right.extract()))
    }

    /// Removes and returns the given item from the right set and its associated item from the left
    /// set.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    ///
    /// let mut map = CycleMap::new();
    /// map.insert(1, "1");
    /// assert_eq!(map.remove_via_right(&"1"), Some((1, "1")));
    /// assert_eq!(map.remove_via_right(&"1"), None);
    /// ```
    pub fn remove_via_right(&mut self, item: &R) -> Option<(L, R)> {
        // This order of these operations matter
        let left = self.table.remove_via_right(item)?;
        let right = self.table.remove_right(item).unwrap();
        Some((left.extract(), right.extract()))
    }

    /// Swaps an item in the left set with another item, remapping the old item's associated right
    /// item to the new left item, and returns the old left item.
    ///
    /// In other words, the pair `(l1, r)` becomes `(l2, r)`.
    ///
    /// If there is another item in the left set that is equal to the new left item which is paired
    /// to another right item, that cycle is removed.
    ///
    /// Note: This method will never return the `SomeRight` variant of `OptionalPair`.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::{CycleMap, OptionalPair::*};
    ///
    /// let mut map: CycleMap<u64, String> = (0..100).map(|i| (i,i.to_string())).collect();
    ///
    /// // 101 is not in the map, so nothing is returned
    /// let op = map.swap_left(&101, 102);
    /// assert_eq!(op, Neither);
    ///
    /// // Swap the 42 in the pair (42, "42") with 101
    /// let op = map.swap_left(&42, 101);
    /// assert_eq!(op, SomeLeft(42));
    /// assert!(map.are_paired(&101, &"42".to_string()));
    ///
    /// // Swap the 84 in the pair (84, "84") with 0 and removes the pair (0, "0")
    /// let op = map.swap_left(&84, 0);
    /// assert_eq!(op, SomeBoth(84, (0, "0".to_string())));
    /// assert!(map.are_paired(&0, &"84".to_string()));
    /// ```
    pub fn swap_left(&mut self, old: &L, new: L) -> OptionalPair<L, (L, R)> {
        // Remove the old left pairing
        let old_l_item = match self.table.remove_left(old) {
            Some(l) => l,
            None => {
                return Neither;
            }
        };
        // Check for Eq left item and remove that cycle if it exists
        let eq_opt = self.remove_via_left(&new);
        // Insert and pair the new item
        let new_l_bucket = self.table.insert_left(new);
        let r_bucket = self.table.find_right(&old_l_item).unwrap();
        let mut r_item = unsafe { r_bucket.as_mut() };
        let mut l_item = unsafe { new_l_bucket.as_mut() };
        // Manually pair the item
        l_item.hash = Some(self.table.hash(&r_item.value));
        r_item.hash = Some(self.table.hash(&l_item.value));
        l_item.id = r_item.id;
        self.table.counter -= 1;
        OptionalPair::from((Some(old_l_item.extract()), eq_opt))
    }

    /// Does what [`swap_left`] does, but fails to swap and returns `Neither` if the old item isn't
    /// paired to the given right item.
    ///
    /// Note: This method will never return the `SomeRight` variant of `OptionalPair`.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::{CycleMap, OptionalPair::*};
    ///
    /// let mut map: CycleMap<u64, String> = (0..100).map(|i| (i,i.to_string())).collect();
    ///
    /// // Swap the 42 in the pair (42, "42") with 101
    /// let op = map.swap_left_checked(&42, &"42".to_string(), 101);
    /// assert_eq!(op, SomeLeft(42));
    /// assert!(map.are_paired(&101, &"42".to_string()));
    ///
    /// // Fails to swap
    /// let op = map.swap_left_checked(&84, &"85".to_string(), 101);
    /// assert_eq!(op, Neither);
    /// assert!(map.are_paired(&84, &"84".to_string()));
    /// ```
    ///
    /// [`swap_left`]: struct.CycleMap.html#method.swap_left
    pub fn swap_left_checked(&mut self, old: &L, expected: &R, new: L) -> OptionalPair<L, (L, R)> {
        // Check if old and expected are paired
        if !self.are_paired(old, expected) {
            return Neither;
        }
        self.swap_left(old, new)
    }

    /// Does what [`swap_left`] does, but inserts a new pair if the old left item isn't in the map.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::{CycleMap, OptionalPair::*};
    ///
    /// let mut map: CycleMap<u64, String> = (0..100).map(|i| (i,i.to_string())).collect();
    ///
    /// // Swap the 42 in the pair (42, "42") with 101
    /// let op = map.swap_left_or_insert(&42, 101, "42".to_string());
    /// assert_eq!(op, SomeLeft(42));
    /// assert!(map.are_paired(&101, &"42".to_string()));
    ///
    /// // Inserts the pair (103, "103") since 102 isn't in the map
    /// let op = map.swap_left_or_insert(&102, 103, "103".to_string());
    /// assert_eq!(op, Neither);
    /// assert!(map.are_paired(&103, &"103".to_string()));
    /// ```
    ///
    /// [`swap_left`]: struct.CycleMap.html#method.swap_left
    pub fn swap_left_or_insert(
        &mut self,
        old: &L,
        new: L,
        to_insert: R,
    ) -> OptionalPair<L, (L, R)> {
        if self.table.contains_left(old) {
            self.swap_left(old, new)
        } else {
            self.insert(new, to_insert).map_left(|(l, _)| l)
        }
    }

    /// Swaps an item in the right set with another item, remapping the old item's associated left
    /// item, and returns the old right item
    ///
    /// In other words, the pair `(l, r1)` becomes `(l, r2)`.
    ///
    /// If there is another item in the left set that is equal to the new left item which is paired
    /// to another right item, that cycle is removed.
    ///
    /// Note: This method will never return the `SomeRight` variant of `OptionalPair`.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::{CycleMap, OptionalPair::*};
    ///
    /// let mut map: CycleMap<u64, String> = (0..100).map(|i| (i,i.to_string())).collect();
    ///
    /// // 101 is not in the map, so nothing is returned
    /// let op = map.swap_right(&"101".to_string(), "102".to_string());
    /// assert_eq!(op, Neither);
    ///
    /// // Swap the "42" in the pair (42, "42") with "101"
    /// let op = map.swap_right(&"42".to_string(), "101".to_string());
    /// assert_eq!(op, SomeLeft("42".to_string()));
    /// assert!(map.are_paired(&42, &"101".to_string()));
    ///
    /// // Swap the "84" in the pair (84, "84") with "0" and removes the pair (0, "0")
    /// let op = map.swap_right(&"84".to_string(), "0".to_string());
    /// assert_eq!(op, SomeBoth("84".to_string(),(0, "0".to_string())));
    /// assert!(map.are_paired(&84, &"0".to_string()));
    /// ```
    pub fn swap_right(&mut self, old: &R, new: R) -> OptionalPair<R, (L, R)>
    {
        // Remove the old left pairing
        let old_r_item = match self.table.remove_right(old) {
            Some(r) => r,
            None => {
                return Neither;
            }
        };
        // Check for Eq left item and remove that cycle if it exists
        let eq_opt = self.remove_via_right(&new);
        // Insert and pair the new item
        let new_r_bucket = self.table.insert_right(new);
        let l_bucket = self.table.find_left(&old_r_item).unwrap();
        let mut l_item = unsafe { l_bucket.as_mut() };
        let mut r_item = unsafe { new_r_bucket.as_mut() };
        // Manually pair the item
        l_item.hash = Some(self.table.hash(&r_item.value));
        r_item.hash = Some(self.table.hash(&l_item.value));
        r_item.id = l_item.id;
        self.table.counter -= 1;
        OptionalPair::from((Some(old_r_item.extract()), eq_opt))
    }

    /// Does what [`swap_right`] does, but fails to swap if the old item isn't paired to the given
    /// left item.
    ///
    /// Note: This method will never return the `SomeRight` variant of `OptionalPair`.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::{CycleMap, OptionalPair::*};
    ///
    /// let mut map: CycleMap<u64, String> = (0..100).map(|i| (i,i.to_string())).collect();
    ///
    /// // Swap the "42" in the pair (42, "42") with "101"
    /// let op = map.swap_right_checked(&"42".to_string(), &42, "101".to_string());
    /// assert_eq!(op, SomeLeft("42".to_string()));
    /// assert!(map.are_paired(&42, &"101".to_string()));
    ///
    /// // Fails to swap
    /// let op = map.swap_right_checked(&"84".to_string(), &85, "101".to_string());
    /// assert_eq!(op, Neither);
    /// assert!(map.are_paired(&84, &"84".to_string()));
    /// ```
    ///
    /// [`swap_right`]: struct.CycleMap.html#method.swap_right
    pub fn swap_right_checked(&mut self, old: &R, expected: &L, new: R) -> OptionalPair<R, (L, R)> {
        // Check if old and expected are paired
        if !self.are_paired(expected, old) {
            return Neither;
        }
        self.swap_right(old, new)
    }

    /// Does what [`swap_right`] does, but inserts a new pair if the old right item isn't in the map.
    ///
    /// Note: This method will never return the `SomeRight` variant of `OptionalPair`.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::{CycleMap, OptionalPair::*};
    ///
    /// let mut map: CycleMap<u64, String> = (0..100).map(|i| (i,i.to_string())).collect();
    ///
    /// // Swap the "42" in the pair (42, "42") with "101"
    /// let op = map.swap_right_or_insert(&"42".to_string(), "101".to_string(), 42);
    /// assert_eq!(op, SomeLeft("42".to_string()));
    /// assert!(map.are_paired(&42, &"101".to_string()));
    ///
    /// // Inserts the pair (103, "103") since 102 isn't in the map
    /// let op = map.swap_right_or_insert(&"102".to_string(), "103".to_string(), 103);
    /// assert_eq!(op, Neither);
    /// assert!(map.are_paired(&103, &"103".to_string()));
    /// ```
    ///
    /// [`swap_right`]: struct.CycleMap.html#method.swap_right
    pub fn swap_right_or_insert(
        &mut self,
        old: &R,
        new: R,
        to_insert: L,
    ) -> OptionalPair<R, (L, R)> {
        if self.table.contains_right(old) {
            self.swap_right(old, new)
        } else {
            self.insert(to_insert, new).map_left(|(_, r)| r)
        }
    }

    /// Gets a reference to an item in the left set using an item in the right set.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    /// let mut map = CycleMap::new();
    /// map.insert(1, "1");
    /// assert_eq!(map.get_left(&"1"), Some(&1));
    /// assert_eq!(map.get_left(&"2"), None);
    /// ```
    pub fn get_left<Q>(&self, item: &Q) -> Option<&L>
    where
        Q: Borrow<R>,
    {
        self.table.get_left(item.borrow()).map(|l| &l.value)
    }

    /// Gets a reference to an item in the right set using an item in the left set.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    /// let mut map = CycleMap::new();
    /// map.insert(1, "1");
    /// assert_eq!(map.get_right(&1), Some(&"1"));
    /// assert_eq!(map.get_right(&2), None);
    /// ```
    pub fn get_right(&self, item: &L) -> Option<&R> {
        self.table.get_right(item).map(|r| &r.value)
    }

    /// Returns an iterator that visits all the pairs in the map in an arbitary order.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    ///
    /// let map: CycleMap<u64, String> = (0..5).map(|i| (i, i.to_string())).collect();
    ///
    /// for (left, right) in map.iter() {
    ///     println!("left: {left}, right: {right}");
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, L, R, S> {
        Iter {
            iter: self.table.iter(),
        }
    }

    /// Returns an iterator over items in the left set in an arbitary order.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    ///
    /// let map: CycleMap<u64, String> = (0..5).map(|i| (i, i.to_string())).collect();
    ///
    /// for left in map.iter_left() {
    ///     println!("left: {left}");
    /// }
    /// ```
    pub fn iter_left(&self) -> SingleIter<'_, L> {
        SingleIter {
            iter: self.table.iter_left(),
        }
    }

    /// Returns an iterator over items in the right set in an arbitary order.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    ///
    /// let map: CycleMap<u64, String> = (0..5).map(|i| (i, i.to_string())).collect();
    ///
    /// for right in map.iter_right() {
    ///     println!("right: {right}");
    /// }
    /// ```
    pub fn iter_right(&self) -> SingleIter<'_, R> {
        SingleIter {
            iter: self.table.iter_right(),
        }
    }

    /// Clears the map, returning all pairs as an iterator while keeping the backing memory
    /// allocated for reuse. If the returned iterator is dropped before being fully consumed, it
    /// drops the remaining pairs.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    ///
    /// let mut map = CycleMap::new();
    /// map.insert(1, "1");
    /// map.insert(2, "2");
    /// let cap = map.capacity();
    ///
    /// for (l, r) in map.drain().take(1) {
    ///     assert!(l == 1 || l == 2);
    ///     assert!(r == "1" || r == "2");
    /// }
    ///
    /// assert!(map.is_empty());
    /// assert_eq!(map.capacity(), cap);
    /// ```
    pub fn drain(&mut self) -> DrainIter<'_, L, R> {
        DrainIter {
            iter: self.table.drain(),
        }
    }

    /// Returns an iterator that removes and yields all pairs that evaluate to `true` in the given
    /// closure while keeping the backing memory allocated.
    ///
    /// If the closure returns `false`, or panics, the element remains in the map and will not be
    /// yielded.
    ///
    /// If the iterator is only partially consumed or not consumed at all, each of the remaining
    /// elements will still be subjected to the closure and removed and dropped if it returns true.
    ///
    /// It is unspecified how many more elements will be subjected to the closure if a panic occurs
    /// in the closure, or a panic occurs while dropping an element, or if the `DrainFilter` value
    /// is leaked.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    ///
    /// let mut map: CycleMap<u64, String> = (0..100).map(|i| (i,i.to_string())).collect();
    ///
    /// // Iterate over the map, remove the pairs with an odd left item
    /// for (l, _) in map.drain_filter(|l,_| l % 2 == 1) {
    ///     assert!(l % 2 == 1);
    /// }
    ///
    /// assert_eq!(map.len(), 50);
    /// ```
    pub fn drain_filter<F>(&mut self, f: F) -> DrainFilterIter<'_, L, R, S, F>
    where
        F: FnMut(&L, &R) -> bool,
    {
        DrainFilterIter {
            f,
            iter: unsafe { self.table.left_set.iter() },
            map_ref: &mut self.table,
        }
    }

    /// Drops all pairs that cause the given closure to return `false`. Pairs are visited in an
    /// arbitary order.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    ///
    /// let mut map: CycleMap<u64, String> = (0..100).map(|i| (i,i.to_string())).collect();
    ///
    /// //Remove all pairs with an odd left item
    /// map.retain(|l, _| l % 2 == 0);
    /// assert_eq!(map.len(), 50);
    ///
    /// for (l, _) in map.iter() {
    ///     assert!(l % 2 == 0);
    /// }
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&L, &R) -> bool,
    {
        for left in unsafe { self.table.left_set.iter() } {
            match self.table.find_right(unsafe { left.as_ref() }) {
                Some(right) => {
                    let l = unsafe { &left.as_ref().value };
                    let r = unsafe { &right.as_ref().value };
                    if !f(l, r) {
                        self.remove(l, r);
                    }
                }
                _ => {
                    unreachable!("Internal state error: Unpaired item found in CycleMap");
                }
            }
        }
    }

    /// Shrinks the capacity of the map with a lower limit. It will drop down no lower than the
    /// supplied limit while maintaining the internal rules and possibly leaving some space in
    /// accordance with the resize policy.
    ///
    /// This function does nothing if the current capacity is smaller than the supplied minimum capacity.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    ///
    /// let mut map: CycleMap<i32, i32> = CycleMap::with_capacity(100);
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to(10);
    /// assert!(map.capacity() >= 10);
    /// map.shrink_to(0);
    /// assert!(map.capacity() >= 2);
    /// map.shrink_to(10);
    /// assert!(map.capacity() >= 2);
    /// ```
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.table.shrink_to_left(min_capacity);
        self.table.shrink_to_right(min_capacity);
    }

    /// Shrinks the capacity of the map as much as possible. It will drop down as much as possible
    /// while maintaining the internal rules and possibly leaving some space in accordance with the
    /// resize policy.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    ///
    /// let mut map: CycleMap<i32, i32> = CycleMap::with_capacity(100);
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to_fit();
    /// assert!(map.capacity() >= 2);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.table.shrink_to_fit();
    }

    /// Reserves capacity for at least additional more elements to be inserted in the HashMap. The
    /// collection may reserve more space to avoid frequent reallocations.
    ///
    /// # Panics
    /// Panics if the new allocation size overflows usize.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    /// let mut map: CycleMap<&str, i32> = CycleMap::new();
    /// map.reserve(10);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.table.reserve_left(additional);
        self.table.reserve_right(additional);
    }

    /// Tries to reserve capacity for at least additional more elements to be inserted in the given
    /// HashMap<K,V>. The collection may reserve more space to avoid frequent reallocations.
    ///
    /// # Errors
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    /// let mut map: CycleMap<&str, isize> = CycleMap::new();
    /// map.try_reserve(10).expect("why is the test harness OMGing on 10 bytes?");
    /// ```
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.table.try_reserve_left(additional)?;
        self.table.try_reserve_right(additional)?;
        Ok(())
    }
}

impl<L, R, S> CycleMap<L, R, S> {
    /// Creates a `CycleMap`and that uses the given hasher.
    ///
    /// Warning: `hash_builder` is normally randomly generated, and is designed to allow
    /// `CycleMap`s to be resistant to attacks that cause many collisions and very poor
    /// performance. Setting it manually using this function can expose a DoS attack vector.
    ///
    /// The `hash_builder` passed should implement the [`BuildHasher`] trait for the CycleMap to be
    /// useful, see its documentation for details.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    /// use std::collections::hash_map::RandomState;
    ///
    /// let s = RandomState::new();
    /// let mut map = CycleMap::with_capacity_and_hasher(10, s);
    /// map.insert(1, "1");
    /// ```
    pub const fn with_hasher(hash_builder: S) -> Self {
        Self {
            table: RawCycleMap::with_hasher(hash_builder),
        }
    }

    /// Creates a `CycleMap` with inner sets that have at least the specified capacity, and that
    /// uses the given hasher.
    ///
    /// The map will be able to hold at least `capacity` many pairs before reallocating.
    ///
    /// Warning: `hash_builder` is normally randomly generated, and is designed to allow
    /// `CycleMap`s to be resistant to attacks that cause many collisions and very poor
    /// performance. Setting it manually using this function can expose a DoS attack vector.
    ///
    /// The `hash_builder` passed should implement the [`BuildHasher`] trait for the CycleMap to be
    /// useful, see its documentation for details.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    /// use std::collections::hash_map::RandomState;
    ///
    /// let s = RandomState::new();
    /// let mut map = CycleMap::with_capacity_and_hasher(10, s);
    /// map.insert(1, "1");
    /// ```
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        Self {
            table: RawCycleMap::with_capacity_and_hasher(capacity, hash_builder),
        }
    }

    /// Returns a reference to the [`BuildHasher`] used by the map
    pub fn hasher(&self) -> &S {
        self.table.hasher()
    }

    /// Returns the number of items that the inner sets can hold without reallocation.
    ///
    /// Note: Only one value is returned since both sets always have the same capacity.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    /// let map: CycleMap<u64, String> = CycleMap::with_capacity(100);
    /// assert!(map.capacity() >= 100);
    /// ```
    pub fn capacity(&self) -> usize {
        // The size of the sets is always equal
        self.table.capacity_left()
    }

    /// Returns the number of items in the inner sets.
    ///
    /// Note: Only one number is returned since both sets always have the name size.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    ///
    /// let mut map = CycleMap::new();
    /// assert_eq!(map.len(), 0);
    /// map.insert(1, "1");
    /// assert_eq!(map.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        // The size of the sets is always equal
        self.table.len_left()
    }

    /// Returns `true` if no items are in the map and `false` otherwise.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    ///
    /// let mut map = CycleMap::new();
    /// assert!(map.is_empty());
    /// map.insert(1, "1");
    /// assert_eq!(map.len(), 1);
    /// assert!(!map.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.table.is_empty()
    }

    /// Removes all items for the map while keeping the backing memory allocated for reuse.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::CycleMap;
    ///
    /// let mut map = CycleMap::new();
    /// assert!(map.is_empty());
    /// map.insert(1, "1");
    /// assert!(!map.is_empty());
    /// map.clear();
    /// assert!(map.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.table.clear();
    }
}

impl<L, R, S> Clone for CycleMap<L, R, S>
where
    L: Eq + Hash + Clone,
    R: Eq + Hash + Clone,
    S: BuildHasher + Clone,
{
    fn clone(&self) -> Self {
        Self {
            table: self.table.clone(),
        }
    }
}

impl<L, R, S> Default for CycleMap<L, R, S>
where
    S: Default,
{
    fn default() -> Self {
        Self::with_hasher(Default::default())
    }
}

impl<L, R, S> fmt::Debug for CycleMap<L, R, S>
where
    L: Hash + Eq + fmt::Debug,
    R: Hash + Eq + fmt::Debug,
    S: BuildHasher,
{
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_set().entries(self.iter()).finish()
    }
}

impl<L, R, S> PartialEq<CycleMap<L, R, S>> for CycleMap<L, R, S>
where
    L: Hash + Eq + Debug,
    R: Hash + Eq + Debug,
    S: BuildHasher,
{
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }
        self.iter().all(|(l, r)| other.are_paired(l, r))
    }
}

impl<L, R, S> Eq for CycleMap<L, R, S>
where
    L: Hash + Eq + Debug,
    R: Hash + Eq + Debug,
    S: BuildHasher,
{
}

impl<L, R, S> Extend<(L, R)> for CycleMap<L, R, S>
where
    L: Hash + Eq + Debug,
    R: Hash + Eq + Debug,
    S: BuildHasher,
{
    #[inline]
    fn extend<T: IntoIterator<Item = (L, R)>>(&mut self, iter: T) {
        for (l, r) in iter {
            self.insert(l, r);
        }
    }
}

impl<L, R> FromIterator<(L, R)> for CycleMap<L, R>
where
    L: Hash + Eq + Debug,
    R: Hash + Eq + Debug,
{
    fn from_iter<T: IntoIterator<Item = (L, R)>>(iter: T) -> Self {
        let mut digest = CycleMap::default();
        digest.extend(iter);
        digest
    }
}

/// An iterator over the entry pairs of a `CycleMap`.
pub struct Iter<'a, L, R, S> {
    iter: RawIter<'a, L, R, S>,
}

impl<L, R, S> Clone for Iter<'_, L, R, S> {
    fn clone(&self) -> Self {
        Self {
            iter: self.iter.clone(),
        }
    }
}

impl<L, R, S> fmt::Debug for Iter<'_, L, R, S>
where
    L: Hash + Eq + fmt::Debug,
    R: Hash + Eq + fmt::Debug,
    S: BuildHasher,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, L, R, S> Iterator for Iter<'a, L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
    type Item = (&'a L, &'a R);

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next()? {
            SomeBoth(l, r) => unsafe { Some((&l.as_ref().value, &r.as_ref().value)) },
            _ => {
                unreachable!("Internal state error: Unpaired item found in CycleMap");
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<L, R, S> ExactSizeIterator for Iter<'_, L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<L, R, S> FusedIterator for Iter<'_, L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
}

/// An iterator over the left elements of a `CycleMap`.
pub struct SingleIter<'a, T> {
    iter: RawSingleIter<'a, T>,
}

impl<T> Clone for SingleIter<'_, T> {
    fn clone(&self) -> Self {
        Self {
            iter: self.iter.clone(),
        }
    }
}

impl<T> fmt::Debug for SingleIter<'_, T>
where
    T: Hash + Eq + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, T> Iterator for SingleIter<'a, T>
where
    T: 'a + Hash + Eq,
{
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|i| unsafe { &i.as_ref().value })
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T> ExactSizeIterator for SingleIter<'_, T>
where
    T: Hash + Eq,
{
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<T> FusedIterator for SingleIter<'_, T> where T: Hash + Eq {}

/// An iterator over the entry pairs of a `CycleMap`.
#[allow(missing_debug_implementations)]
pub struct DrainIter<'a, L, R>
where
    L: Hash + Eq,
    R: Hash + Eq,
{
    iter: RawDrainIter<'a, L, R>,
}

impl<'a, L, R> Iterator for DrainIter<'a, L, R>
where
    L: Hash + Eq,
    R: Hash + Eq,
{
    type Item = (L, R);

    fn next(&mut self) -> Option<Self::Item> {
        match self.iter.next()? {
            SomeBoth(l, r) => Some((l.extract(), r.extract())),
            _ => {
                unreachable!("Internal state error: Unpaired item found in CycleMap");
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<L, R> ExactSizeIterator for DrainIter<'_, L, R>
where
    L: Hash + Eq,
    R: Hash + Eq,
{
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<L, R> FusedIterator for DrainIter<'_, L, R>
where
    L: Hash + Eq,
    R: Hash + Eq,
{
}

/// A draining iterator over entries of a `CycleMap` which satisfy the predicate `f`.
#[allow(missing_debug_implementations)]
pub struct DrainFilterIter<'a, L, R, S, F>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
    F: FnMut(&L, &R) -> bool,
{
    f: F,
    iter: hashbrown::raw::RawIter<MappingItem<L>>,
    map_ref: &'a mut RawCycleMap<L, R, S>,
}

struct ConsumeAllOnDrop<'a, T: Iterator>(&'a mut T);

impl<T: Iterator> Drop for ConsumeAllOnDrop<'_, T> {
    fn drop(&mut self) {
        self.0.for_each(drop)
    }
}

impl<'a, L, R, S, F> Drop for DrainFilterIter<'a, L, R, S, F>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
    F: FnMut(&L, &R) -> bool,
{
    fn drop(&mut self) {
        while let Some(item) = self.next() {
            let guard = ConsumeAllOnDrop(self);
            drop(item);
            mem::forget(guard);
        }
    }
}

impl<L, R, S, F> Iterator for DrainFilterIter<'_, L, R, S, F>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
    F: FnMut(&L, &R) -> bool,
{
    type Item = (L, R);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(left) = self.iter.next() {
            match self.map_ref.find_right(unsafe { left.as_ref() }) {
                Some(right) => {
                    let l = unsafe { &left.as_ref().value };
                    let r = unsafe { &right.as_ref().value };
                    if (self.f)(l, r) {
                        let (left, right) = self.map_ref.remove(l, r).unwrap();
                        return Some((left.extract(), right.extract()));
                    } else {
                        continue;
                    }
                }
                _ => {
                    unreachable!("Internal state error: Unpaired item found in CycleMap");
                }
            }
        }
        None
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<L, R, S, F> FusedIterator for DrainFilterIter<'_, L, R, S, F>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
    F: FnMut(&L, &R) -> bool,
{
}
