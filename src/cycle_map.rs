use std::{
    borrow::Borrow,
    default::Default,
    fmt,
    hash::{BuildHasher, Hash},
    iter::FusedIterator,
    marker::PhantomData,
};

use core::mem;

use hashbrown::{
    hash_map::DefaultHashBuilder,
    raw::{RawDrain, RawIter, RawTable},
    TryReserveError,
};

use crate::optionals::*;
use crate::utils::*;
use OptionalPair::*;

#[cfg(doc)]
use hashbrown::HashMap;

// Contains a value and the hash of the item that the value maps to.
pub(crate) struct MappingPair<T> {
    pub(crate) value: T,
    pub(crate) hash: u64,
    pub(crate) id: u64,
}

pub(crate) fn equivalent_key<Q: PartialEq + ?Sized>(
    k: &Q,
) -> impl Fn(&MappingPair<Q>) -> bool + '_ {
    move |x| k.eq(&x.value)
}

pub(crate) fn hash_and_id<'a, Q: PartialEq + ?Sized>(
    hash: u64,
    id: u64,
) -> impl Fn(&MappingPair<Q>) -> bool + 'a {
    move |x| id == x.id && hash == x.hash
}

pub(crate) fn just_id<'a, Q: PartialEq + ?Sized>(id: u64) -> impl Fn(&MappingPair<Q>) -> bool + 'a {
    move |x| id == x.id
}

/// A hash map implementation that allows bi-directional, constant time lookups.
///
/// CycleMap bijectively maps two sets together.
/// In other words, every item in a set is mapped to one and only one item in the other set.
/// It does this while maintaining the same complexitity for lookups
/// as a traditional hash map and while only keeping a single copy of each element.
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
    pub(crate) hash_builder: St,
    pub(crate) counter: u64,
    left_set: RawTable<MappingPair<L>>,
    right_set: RawTable<MappingPair<R>>,
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
    /// Creates a new, empty `CycleMap` with inner sets that each have at least the given capacity
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
    L: Eq + Hash,
    R: Eq + Hash,
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
        let digest = InsertOptional::from((opt_from_left, opt_from_right));
        let l_hash = make_hash::<L, S>(&self.hash_builder, &left);
        let r_hash = make_hash::<R, S>(&self.hash_builder, &right);
        let left_pairing = MappingPair {
            value: left,
            hash: r_hash,
            id: self.counter,
        };
        let right_pairing = MappingPair {
            value: right,
            hash: l_hash,
            id: self.counter,
        };
        self.counter += 1;
        self.left_set.insert(
            l_hash,
            left_pairing,
            make_hasher::<MappingPair<L>, S>(&self.hash_builder),
        );
        self.right_set.insert(
            r_hash,
            right_pairing,
            make_hasher::<MappingPair<R>, S>(&self.hash_builder),
        );
        digest
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
        let l_hash = make_hash::<L, S>(&self.hash_builder, left);
        let r_hash = make_hash::<R, S>(&self.hash_builder, right);
        let opt_left = self.left_set.get(l_hash, equivalent_key(left));
        let opt_right = self.right_set.get(r_hash, equivalent_key(right));
        match (opt_left, opt_right) {
            (Some(left), Some(right)) => {
                left.id == right.id && l_hash == right.hash && r_hash == left.hash
            }
            _ => false,
        }
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
        let hash = make_hash::<L, S>(&self.hash_builder, left);
        self.left_set.get(hash, equivalent_key(left)).is_some()
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
        let hash = make_hash::<R, S>(&self.hash_builder, right);
        self.right_set.get(hash, equivalent_key(right)).is_some()
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
        let l_hash = make_hash::<L, S>(&self.hash_builder, item);
        let left_pairing: MappingPair<L> =
            self.left_set.remove_entry(l_hash, equivalent_key(item))?;
        let right_pairing = self
            .right_set
            .remove_entry(left_pairing.hash, hash_and_id(l_hash, left_pairing.id))
            .unwrap();
        Some((left_pairing.extract(), right_pairing.extract()))
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
        let r_hash = make_hash::<R, S>(&self.hash_builder, item);
        let right_pairing: MappingPair<R> =
            self.right_set.remove_entry(r_hash, equivalent_key(item))?;
        let left_pairing = self
            .left_set
            .remove_entry(right_pairing.hash, hash_and_id(r_hash, right_pairing.id))
            .unwrap();
        Some((left_pairing.extract(), right_pairing.extract()))
    }

    /// Removes a pair using the hash of the left item, right item, and their shared pairing id
    fn remove_via_hashes_and_id(&mut self, l_hash: u64, r_hash: u64, id: u64) -> Option<(L, R)> {
        let left_pairing = self
            .left_set
            .remove_entry(l_hash, hash_and_id(r_hash, id))?;
        let right_pairing = self
            .right_set
            .remove_entry(r_hash, hash_and_id(l_hash, id))
            .unwrap();
        Some((left_pairing.extract(), right_pairing.extract()))
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
        // Check for Eq left item and remove that cycle if it exists
        let new_l_hash = make_hash::<L, S>(&self.hash_builder, &new);
        let eq_opt = self.swap_left_eq_check(old, &new, new_l_hash);
        // Find the old left pairing
        let old_l_hash = make_hash::<L, S>(&self.hash_builder, old);
        let l_pairing: &MappingPair<L> = match self.left_set.get(old_l_hash, equivalent_key(old)) {
            Some(p) => p,
            None => {
                return Neither;
            }
        };
        // Use old left pairing to find right pairing
        let r_pairing: &mut MappingPair<R> = self
            .right_set
            .get_mut(l_pairing.hash, hash_and_id(old_l_hash, l_pairing.id))
            .unwrap();
        // Updated right pairing
        r_pairing.hash = new_l_hash;
        // Create new left pairing
        let new_left_pairing: MappingPair<L> = MappingPair {
            value: new,
            hash: l_pairing.hash,
            id: l_pairing.id,
        };
        // Remove old left pairing
        let old_left_item: L = self
            .left_set
            .remove_entry(old_l_hash, equivalent_key(old))
            .unwrap()
            .extract();
        // Insert new left pairing
        self.left_set.insert(
            new_l_hash,
            new_left_pairing,
            make_hasher::<MappingPair<L>, S>(&self.hash_builder),
        );
        // Return old left pairing
        OptionalPair::from((Some(old_left_item), eq_opt))
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
        let old_l_hash = make_hash::<L, S>(&self.hash_builder, old);
        if self.left_set.get(old_l_hash, equivalent_key(old)).is_some() {
            self.swap_left(old, new)
        } else {
            // TODO: Do further verification on this. All cases _should_ be covered here as this
            // insert should never return a left pair
            self.insert(new, to_insert).map_left(|(l, _)| l)
        }
    }

    /// Pair of the collision checks done in the swap left methods
    fn swap_left_eq_check(&mut self, old: &L, new: &L, new_hash: u64) -> Option<(L, R)> {
        self.left_set.get(new_hash, equivalent_key(new))?;
        if new != old {
            // Remove the problem cycle
            self.remove_via_left(new)
        } else {
            // If old and new are the same, they we are updating an cycle
            None
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
    pub fn swap_right(&mut self, old: &R, new: R) -> OptionalPair<R, (L, R)> {
        // Check for Eq left item and remove that cycle if it exists
        let new_r_hash = make_hash::<R, S>(&self.hash_builder, &new);
        let eq_opt = self.swap_right_eq_check(old, &new, new_r_hash);
        // Find the old right pairing
        let old_r_hash = make_hash::<R, S>(&self.hash_builder, old);
        let r_pairing: &MappingPair<R> = match self.right_set.get(old_r_hash, equivalent_key(old)) {
            Some(p) => p,
            None => {
                return Neither;
            }
        };
        // Use old right pairing to find the left pairing
        let l_pairing: &mut MappingPair<L> = self
            .left_set
            .get_mut(r_pairing.hash, hash_and_id(old_r_hash, r_pairing.id))
            .unwrap();
        // Updated left pairing
        let new_r_hash = make_hash::<R, S>(&self.hash_builder, &new);
        l_pairing.hash = new_r_hash;
        // Create new right pairing
        let new_right_pairing = MappingPair {
            value: new,
            hash: r_pairing.hash,
            id: r_pairing.id,
        };
        // Remove old right pairing
        let old_right_item: R = self
            .right_set
            .remove_entry(old_r_hash, equivalent_key(old))
            .unwrap()
            .extract();
        // Insert new right pairing
        self.right_set.insert(
            new_r_hash,
            new_right_pairing,
            make_hasher::<MappingPair<R>, S>(&self.hash_builder),
        );
        // Return old right pairing
        OptionalPair::from((Some(old_right_item), eq_opt))
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
        } // Things can be removed after this point
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
        // Find the old right pairing
        let old_r_hash = make_hash::<R, S>(&self.hash_builder, old);
        if self
            .right_set
            .get(old_r_hash, equivalent_key(old))
            .is_some()
        {
            self.swap_right(old, new)
        } else {
            // TODO: Do further verification on this. All cases _should_ be covered here
            match self.insert(to_insert, new) {
                InsertOptional::Neither => Neither,
                InsertOptional::SomeRight(pair) => SomeRight(pair),
                _ => {
                    unreachable!("There isn't a left item")
                }
            }
        }
    }

    /// Pair of the collision checks done in the swap left methods
    fn swap_right_eq_check(&mut self, old: &R, new: &R, new_hash: u64) -> Option<(L, R)> {
        self.right_set.get(new_hash, equivalent_key(new))?;
        if new != old {
            // Remove the problem cycle
            self.remove_via_right(new)
        } else {
            // If old and new are the same, they we are updating an cycle
            None
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
        let r_hash = make_hash::<R, S>(&self.hash_builder, item.borrow());
        let right_pairing: &MappingPair<R> =
            self.get_right_inner_with_hash(item.borrow(), r_hash)?;
        match self
            .left_set
            .get(right_pairing.hash, hash_and_id(r_hash, right_pairing.id))
        {
            None => None,
            Some(pairing) => Some(&pairing.value),
        }
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
        let l_hash = make_hash::<L, S>(&self.hash_builder, item);
        let left_pairing: &MappingPair<L> = self.get_left_inner_with_hash(item, l_hash)?;
        match self
            .right_set
            .get(left_pairing.hash, hash_and_id(l_hash, left_pairing.id))
        {
            None => None,
            Some(pairing) => Some(&pairing.value),
        }
    }

    /* Might be used in the future
    /// Removes a pair using the hash of the left item, right item, and their shared pairing id
    fn get_via_hashes_and_id(&mut self, l_hash: u64, r_hash: u64, id: u64) -> Option<(&L, &R)> {
    let left_pairing = self.left_set.get(l_hash, hash_and_id(r_hash, id))?;
    let right_pairing = self.right_set.get(r_hash, hash_and_id(l_hash, id)).unwrap();
    Some((&left_pairing.value, &right_pairing.value))
    }
    */

    #[inline]
    fn get_left_inner(&self, item: &L) -> Option<&MappingPair<L>> {
        let hash = make_hash::<L, S>(&self.hash_builder, item);
        self.left_set.get(hash, equivalent_key(item))
    }

    #[inline]
    fn get_left_inner_with_hash(&self, item: &L, hash: u64) -> Option<&MappingPair<L>> {
        self.left_set.get(hash, equivalent_key(item))
    }

    #[inline]
    fn get_right_inner_with_hash(&self, item: &R, hash: u64) -> Option<&MappingPair<R>> {
        self.right_set.get(hash, equivalent_key(item))
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
            left_iter: unsafe { self.left_set.iter() },
            map_ref: self,
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
            iter: unsafe { self.left_set.iter() },
            marker: PhantomData,
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
            iter: unsafe { self.right_set.iter() },
            marker: PhantomData,
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
        self.counter = 0;
        DrainIter {
            left_iter: self.left_set.drain(),
            right_ref: &mut self.right_set,
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
    pub fn drain_filter<F>(&mut self, f: F) -> DrainFilterIter<'_, L, R, F>
    where
        F: FnMut(&L, &R) -> bool,
    {
        DrainFilterIter {
            f,
            inner: DrainFilterInner {
                left_iter: unsafe { self.left_set.iter() },
                left_ref: &mut self.left_set,
                right_ref: &mut self.right_set,
            },
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
        let mut to_drop: Vec<(u64, u64, u64)> = Vec::with_capacity(self.left_set.len());
        for (left, right) in self.iter() {
            if !f(left, right) {
                let l_hash = make_hash::<L, S>(&self.hash_builder, left);
                let r_hash = make_hash::<R, S>(&self.hash_builder, right);
                let id = self.get_left_inner(left).unwrap().id;
                to_drop.push((l_hash, r_hash, id));
            }
        }
        for (l_hash, r_hash, id) in to_drop {
            self.remove_via_hashes_and_id(l_hash, r_hash, id);
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
        self.left_set
            .shrink_to(min_capacity, make_hasher(&self.hash_builder));
        self.right_set
            .shrink_to(min_capacity, make_hasher(&self.hash_builder));
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
        self.left_set
            .shrink_to(self.len(), make_hasher(&self.hash_builder));
        self.right_set
            .shrink_to(self.len(), make_hasher(&self.hash_builder));
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
        self.left_set
            .reserve(additional, make_hasher(&self.hash_builder));
        self.right_set
            .reserve(additional, make_hasher(&self.hash_builder));
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
        self.left_set
            .try_reserve(additional, make_hasher(&self.hash_builder))?;
        self.right_set
            .try_reserve(additional, make_hasher(&self.hash_builder))?;
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
            hash_builder,
            counter: 0,
            left_set: RawTable::new(),
            right_set: RawTable::new(),
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
            hash_builder,
            counter: 0,
            left_set: RawTable::with_capacity(capacity),
            right_set: RawTable::with_capacity(capacity),
        }
    }

    /// Returns a reference to the [`BuildHasher`] used by the map
    pub fn hasher(&self) -> &S {
        &self.hash_builder
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
        self.left_set.capacity()
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
        self.left_set.len()
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
        self.len() == 0
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
    /// assert_eq!(map.len(), 1);
    /// assert!(!map.is_empty());
    /// map.clear();
    /// assert!(map.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.left_set.clear();
        self.right_set.clear();
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
            left_set: self.left_set.clone(),
            right_set: self.right_set.clone(),
            counter: self.counter,
            hash_builder: self.hash_builder.clone(),
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
    L: Hash + Eq,
    R: Hash + Eq,
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
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
}

impl<L, R, S> Extend<(L, R)> for CycleMap<L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
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
    L: Hash + Eq,
    R: Hash + Eq,
{
    fn from_iter<T: IntoIterator<Item = (L, R)>>(iter: T) -> Self {
        let mut digest = CycleMap::default();
        digest.extend(iter);
        digest
    }
}

/// An iterator over the entry pairs of a `CycleMap`.
pub struct Iter<'a, L, R, S> {
    left_iter: RawIter<MappingPair<L>>,
    map_ref: &'a CycleMap<L, R, S>,
}

impl<L, R, S> Clone for Iter<'_, L, R, S> {
    fn clone(&self) -> Self {
        Self {
            left_iter: self.left_iter.clone(),
            map_ref: self.map_ref,
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
        match self.left_iter.next() {
            Some(l) => unsafe {
                let left = &l.as_ref().value;
                let right = self.map_ref.get_right(left).unwrap();
                Some((left, right))
            },
            None => None,
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.left_iter.size_hint()
    }
}

impl<L, R, S> ExactSizeIterator for Iter<'_, L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
    fn len(&self) -> usize {
        self.left_iter.len()
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
    iter: RawIter<MappingPair<T>>,
    marker: PhantomData<&'a T>,
}

impl<T> Clone for SingleIter<'_, T> {
    fn clone(&self) -> Self {
        Self {
            iter: self.iter.clone(),
            marker: PhantomData,
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
        match self.iter.next() {
            Some(item) => {
                let val = unsafe { &item.as_ref().value };
                Some(val)
            }
            None => None,
        }
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
pub struct DrainIter<'a, L, R> {
    left_iter: RawDrain<'a, MappingPair<L>>,
    right_ref: &'a mut RawTable<MappingPair<R>>,
}

impl<'a, L, R> Iterator for DrainIter<'a, L, R>
where
    L: Hash + Eq,
    R: Hash + Eq,
{
    type Item = (L, R);

    fn next(&mut self) -> Option<Self::Item> {
        let left = self.left_iter.next()?;
        let right = self
            .right_ref
            .remove_entry(left.hash, just_id(left.id))
            .unwrap();
        Some((left.extract(), right.extract()))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.left_iter.size_hint()
    }
}

impl<L, R> ExactSizeIterator for DrainIter<'_, L, R>
where
    L: Hash + Eq,
    R: Hash + Eq,
{
    fn len(&self) -> usize {
        self.left_iter.len()
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
pub struct DrainFilterIter<'a, L, R, F>
where
    R: Eq,
    F: FnMut(&L, &R) -> bool,
{
    f: F,
    inner: DrainFilterInner<'a, L, R>,
}

impl<'a, L, R, F> Drop for DrainFilterIter<'a, L, R, F>
where
    R: Eq,
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

pub(super) struct ConsumeAllOnDrop<'a, T: Iterator>(pub(super) &'a mut T);

impl<T: Iterator> Drop for ConsumeAllOnDrop<'_, T> {
    fn drop(&mut self) {
        self.0.for_each(drop)
    }
}

impl<L, R: Eq, F> Iterator for DrainFilterIter<'_, L, R, F>
where
    F: FnMut(&L, &R) -> bool,
{
    type Item = (L, R);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next(&mut self.f)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.inner.left_iter.size_hint().1)
    }
}

impl<L, R: Eq, F> FusedIterator for DrainFilterIter<'_, L, R, F> where F: FnMut(&L, &R) -> bool {}

/// Portions of `DrainFilter` shared with `set::DrainFilter`
pub(super) struct DrainFilterInner<'a, L, R> {
    pub(super) left_iter: RawIter<MappingPair<L>>,
    pub(super) left_ref: &'a mut RawTable<MappingPair<L>>,
    pub(super) right_ref: &'a mut RawTable<MappingPair<R>>,
}

impl<L, R: Eq> DrainFilterInner<'_, L, R> {
    pub(super) fn next<F>(&mut self, f: &mut F) -> Option<(L, R)>
    where
        F: FnMut(&L, &R) -> bool,
    {
        unsafe {
            while let Some(left) = self.left_iter.next() {
                let l_pairing = left.as_ref();
                let right = self
                    .right_ref
                    .find(l_pairing.hash, just_id(l_pairing.id))
                    .unwrap();
                if f(&l_pairing.value, &right.as_ref().value) {
                    let l = self.left_ref.remove(left).extract();
                    let r = self.right_ref.remove(right).extract();
                    return Some((l, r));
                }
            }
        }
        None
    }
}

impl<T> MappingPair<T> {
    // Consumes the pair and returns the held `T`
    pub(crate) fn extract(self) -> T {
        self.value
    }
}

impl<T: Hash> Hash for MappingPair<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value.hash(state)
    }
}

impl<T: PartialEq> PartialEq for MappingPair<T> {
    fn eq(&self, other: &Self) -> bool {
        self.id.eq(&other.id) && self.value.eq(&other.value)
    }
}

impl<T: PartialEq> PartialEq<T> for MappingPair<T> {
    fn eq(&self, other: &T) -> bool {
        self.value.eq(other)
    }
}

impl<T: Eq> Eq for MappingPair<T> {}

impl<T: Clone> Clone for MappingPair<T> {
    fn clone(&self) -> Self {
        Self {
            value: self.value.clone(),
            hash: self.hash,
            id: self.id,
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for MappingPair<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "MappingPair {{ value: {:?}, hash: {}, id: {} }}",
            self.value, self.hash, self.id
        )
    }
}
