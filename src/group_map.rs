use std::{
    borrow::Borrow,
    default::Default,
    fmt,
    hash::{BuildHasher, Hash},
    iter::FusedIterator,
    marker::PhantomData,
    ops::AddAssign,
};

use hashbrown::{
    hash_map::DefaultHashBuilder,
    hash_set,
    raw::{RawIter, RawTable},
    HashSet,
};

use crate::utils::*;

#[cfg(doc)]
use hashbrown::HashMap;

pub(crate) fn equivalent_key_left<T: Borrow<Q>, Q: PartialEq + ?Sized>(
    k: &Q,
) -> impl Fn(&LeftItem<T>) -> bool + '_ {
    move |x| x.value.borrow().eq(k)
}

pub(crate) fn equivalent_key_right<T: Borrow<Q>, Q: PartialEq + ?Sized>(
    k: &Q,
) -> impl Fn(&RightItem<T>) -> bool + '_ {
    move |x| x.value.borrow().eq(k)
}

pub(crate) fn left_with_left_id<T: PartialEq + ?Sized>(id: ID) -> impl Fn(&LeftItem<T>) -> bool {
    move |x| x.id == id
}

/*
pub(crate) fn left_with_right_id<T: PartialEq + ?Sized>(id: ID) -> impl Fn(&LeftItem<T>) -> bool {
    move |x| x.r_id == id
}
*/

pub(crate) fn right_with_left_pair<T: PartialEq + ?Sized>(
    pair: &(u64, ID),
) -> impl Fn(&RightItem<T>) -> bool + '_ {
    move |x| x.pairs.contains(pair)
}

pub(crate) fn right_with_right_id<T: PartialEq + ?Sized>(id: ID) -> impl Fn(&RightItem<T>) -> bool {
    move |x| x.id == id
}

// It is fair too easy to switch hashes and ids by accident. Let's fix that.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub(crate) struct ID(u64);

// Contains a value and the hash of the item that the value maps to.
pub(crate) struct LeftItem<T> {
    pub(crate) value: T,
    pub(crate) hash: u64,
    pub(crate) r_id: ID,
    pub(crate) id: ID,
}

// Contains a value and the hash of the item that the value maps to.
pub(crate) struct RightItem<T> {
    pub(crate) value: T,
    pub(crate) pairs: HashSet<(u64, ID)>, // (hash, id) of the paired left items
    pub(crate) id: ID,                    // Right items don't have to be paired, so an id is needed
}

/// A hash map implementation that allows bi-directional, near-constant time lookups.
///
/// Unlike `CycleMap` which bijectively maps two sets together, a `GroupMap` weakly
/// [`surjectively`] maps two sets together. In other words, every item in the left set much be
/// paired to an item in the right set, but two left items are allowed to be paired with the same
/// right item. The "weak" surjectivity comes from the fact that not all right items have to be
/// paired to anything.
///
/// Like the other map types in this crate, `GroupMap` is built on tap of the [`HashMap`]
/// implemented in [`hashbrown`]. As such, it uses the same default hashing algorithm as
/// `hashbrown`'s `HashMap`.
///
/// Moreover, the requirements for a "key" for a `HashMap` is required for all values of a
/// `GroupMap`, namely [`Eq`] and [`Hash`].
///
/// Because multiple left items can be paired with a right item, right-to-left lookups aren't
/// strickly constant time. Instead, right-to-left lookups are implemented with an iterator. This
/// means that, while a `GroupMap` *can* do everything a `CycleMap` can do, they shouldn't be used
/// interchangeably. Because `GroupMap`s maintain weaker invariant, they are generally slower.
///
/// Note: left-to-right lookups maintain the same lookup complexity as other maps, albeit with
/// slightly more operations.
///
/// # Examples
/// ```
/// use cycle_map::GroupMap;
///
/// let values: Vec<(&str, u64)> =
///              vec![ ("zero", 0), ("0", 0),
///                    ("one", 1), ("1", 1),
///                    ("two", 2), ("2", 2),
///                    ("three", 3), ("3", 3),
///                    ("four", 4), ("4", 4), ];
///
/// let mut converter: GroupMap<&str, u64> = values.iter().cloned().collect();
///
/// // The map should contain 10 items in the left set ...
/// assert_eq!(converter.len_left(), 10);
/// // ... and 5 in the right set
/// assert_eq!(converter.len_right(), 5);
///
/// // See if your value number is here
/// if converter.contains_right(&42) {
///     println!( "I know the answer to life!!" );
/// }
///
/// // Get a value from either side!
/// assert!(converter.contains_right(&0));
/// assert_eq!(converter.get_right(&"zero"), Some(&0));
/// assert_eq!(converter.get_right(&"0"), Some(&0));
/// let mut opt_left_iter = converter.get_left_iter(&0);
/// assert!(opt_left_iter.is_some());
/// for l in opt_left_iter.unwrap() {
///     assert!( l == &"zero" || l == &"0" );
/// }
///
/// // Removing a left item removes just that item
/// converter.remove_left(&"zero");
/// assert!(!converter.contains_left(&"zero"));
/// assert!(converter.contains_left(&"0"));
/// let mut opt_left_iter = converter.get_left_iter(&0);
/// assert_eq!(converter.get_left_iter(&0).unwrap().len(), 1);
///
/// // While removing a right item removes it and everything its paired with
/// let (left_items, _) = converter.remove_right(&1).unwrap();
/// println!("{left_items:?}");
/// assert_eq!(left_items.len(), 2);
/// assert!(!converter.contains_left(&"one"));
/// assert!(!converter.contains_left(&"1"));
/// assert!(!converter.contains_right(&1));
///
/// // Items can be repaired in-place!
/// assert!(converter.pair(&"three", &4));
/// assert!(converter.are_paired(&"three", &4));
/// assert!(!converter.are_paired(&"three", &3));
/// ```
///
/// [`surjectively`]: https://en.wikipedia.org/wiki/Surjective_function
pub struct GroupMap<L, R, St = DefaultHashBuilder> {
    pub(crate) hash_builder: St,
    pub(crate) left_counter: ID,
    pub(crate) right_counter: ID,
    left_set: RawTable<LeftItem<L>>,
    right_set: RawTable<RightItem<R>>,
}

impl<L, R> GroupMap<L, R, DefaultHashBuilder> {
    #[inline]
    /// Creates a new, empty `GroupMap`.
    /// The capacity of the new map will be 0.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    /// let map: GroupMap<u64, String> = GroupMap::new();
    /// ```
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    /// Creates a new, empty `GroupMap` with inner sets that each have at least the given capacity.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    /// let map: GroupMap<u64, String> = GroupMap::with_capacity(100);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, DefaultHashBuilder::default())
    }
}

impl<L, R, S> GroupMap<L, R, S>
where
    L: Eq + Hash,
    R: Eq + Hash,
    S: BuildHasher,
{
    /// Adds a pair of items to the map.
    ///
    /// If the map contains a left item that is equal to `left` already, that item is paired with
    /// the new `right` item. Similarly, if the map contain a right item that is equal to `right`,
    /// the new `left` item is paired with the existing right item.
    ///
    /// If you want to remove old items, use [`insert_remove`].
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    ///
    /// let mut map: GroupMap<String, u64> = (0..5).map(|i| (i.to_string(), i)).collect();
    ///
    /// // Simply insert a pair of new items
    /// assert!(!map.contains_left(&5.to_string()));
    /// assert!(!map.contains_right(&5));
    /// map.insert(5.to_string(), 5);
    /// assert!(map.are_paired(&5.to_string(), &5));
    ///
    /// // Pair "0" with a number, keep 0 in the map
    /// map.insert(0.to_string(), 10);
    /// assert!(map.contains_right(&0));
    /// assert!(!map.are_paired(&0.to_string(), &0));
    /// assert!(map.are_paired(&0.to_string(), &10));
    ///
    /// // Let's pair 0 with some new value
    /// map.insert(10.to_string(), 0);
    /// assert!(map.are_paired(&10.to_string(), &0));
    ///
    /// // Swap existing values
    /// map.insert(2.to_string(), 4);
    /// assert!(map.are_paired(&2.to_string(), &4));
    /// assert!(map.are_paired(&4.to_string(), &4));
    /// assert!(!map.are_paired(&2.to_string(), &2));
    /// ```
    ///
    /// [`insert_remove`]: #method.insert_remove
    pub fn insert(&mut self, left: L, right: R) {
        let l_hash = make_hash::<L, S>(&self.hash_builder, &left);
        let r_hash = make_hash::<R, S>(&self.hash_builder, &right);
        let opt_left = self.left_set.get_mut(l_hash, equivalent_key_left(&left));
        let opt_right = self.right_set.get_mut(r_hash, equivalent_key_right(&right));
        match (opt_left, opt_right) {
            (None, None) => {
                let left_item = LeftItem {
                    value: left,
                    hash: r_hash,
                    r_id: self.right_counter,
                    id: self.left_counter,
                };
                self.left_set
                    .insert(l_hash, left_item, make_hasher(&self.hash_builder));
                let mut set = HashSet::with_capacity(1);
                set.insert((l_hash, self.left_counter));
                let right_item = RightItem {
                    value: right,
                    pairs: set,
                    id: self.right_counter,
                };
                self.right_set
                    .insert(r_hash, right_item, make_hasher(&self.hash_builder));
                self.left_counter.0 += 1;
                self.right_counter.0 += 1;
            }
            (Some(l), None) => {
                let pair = (l_hash, l.id);
                let r = self
                    .right_set
                    .get_mut(l.hash, right_with_left_pair(&pair))
                    .unwrap();
                l.hash = r_hash;
                l.r_id = self.right_counter;
                r.pairs.remove(&pair);
                let mut set = HashSet::with_capacity(1);
                set.insert(pair);
                let right_item = RightItem {
                    value: right,
                    pairs: set,
                    id: self.right_counter,
                };
                self.right_set
                    .insert(r_hash, right_item, make_hasher(&self.hash_builder));
                self.right_counter.0 += 1;
            }
            (None, Some(r)) => {
                r.pairs.insert((l_hash, self.left_counter));
                let left_item = LeftItem {
                    value: left,
                    hash: r_hash,
                    id: self.left_counter,
                    r_id: r.id,
                };
                self.left_set
                    .insert(l_hash, left_item, make_hasher(&self.hash_builder));
                self.left_counter.0 += 1;
            }
            (Some(l), Some(r)) => {
                let pair = (l_hash, l.id);
                r.pairs.insert(pair);
                let new_r_id = r.id;
                self.right_set
                    .get_mut(l.hash, right_with_right_id(l.r_id))
                    .unwrap()
                    .pairs
                    .remove(&pair);
                l.hash = r_hash;
                l.r_id = new_r_id;
            }
        }
    }

    /// Adds a pair of items to the map.
    ///
    /// If the map contains a left item that is equal to the new `left` item, it is removed.
    /// If the map contains a right item that is equal to the new `right` item, it and every left
    /// it is paired with is removed.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    ///
    /// let mut map: GroupMap<String, u64> = (0..5).map(|i| (i.to_string(), i)).collect();
    ///
    /// // Simply insert a pair of new items
    /// assert!(!map.contains_left(&5.to_string()));
    /// assert!(!map.contains_right(&5));
    /// map.insert(5.to_string(), 5);
    /// assert!(map.are_paired(&5.to_string(), &5));
    ///
    /// // Pair "0" with a number, keep 0 in the map
    /// map.insert(0.to_string(), 10);
    /// assert!(map.contains_right(&0));
    /// assert!(!map.are_paired(&0.to_string(), &0));
    /// assert!(map.are_paired(&0.to_string(), &10));
    ///
    /// // Let's pair 0 with some new value
    /// map.insert(10.to_string(), 0);
    /// assert!(map.are_paired(&10.to_string(), &0));
    ///
    /// // Swap existing values
    /// map.insert(2.to_string(), 4);
    /// assert!(map.are_paired(&2.to_string(), &4));
    /// assert!(map.are_paired(&4.to_string(), &4));
    /// assert!(!map.are_paired(&2.to_string(), &2));
    /// ```
    ///
    /// [`insert_remove`]: #method.insert_remove
    pub fn insert_remove(&mut self, left: L, right: R) -> (Option<L>, Option<(HashSet<L>, R)>) {
        let opt_from_left = self.remove_left(&left);
        let opt_from_right = self.remove_right(&right);
        let digest = (opt_from_left, opt_from_right);
        let l_hash = make_hash::<L, S>(&self.hash_builder, &left);
        let r_hash = make_hash::<R, S>(&self.hash_builder, &right);
        let left_item = LeftItem {
            value: left,
            hash: r_hash,
            id: self.left_counter,
            r_id: self.right_counter,
        };
        let mut set = HashSet::with_capacity(1);
        set.insert((l_hash, self.left_counter));
        let right_item = RightItem {
            value: right,
            pairs: set,
            id: self.right_counter,
        };
        self.left_counter.0 += 1;
        self.right_counter.0 += 1;
        self.left_set
            .insert(l_hash, left_item, make_hasher(&self.hash_builder));
        self.right_set
            .insert(r_hash, right_item, make_hasher(&self.hash_builder));
        digest
    }

    /// Adds an item to the left set of the map.
    ///
    /// Should this item be equal to another, the old item is removed.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    ///
    /// let mut map: GroupMap<String, u64> = (0..5).map(|i| (i.to_string(), i)).collect();
    ///
    /// // Let's pair 0 with a second item
    /// let opt = map.insert_left("zero".to_string(), &0);
    /// assert!(opt.is_none());
    /// assert!(map.are_paired(&0.to_string(), &0));
    /// assert!(map.are_paired(&"zero".to_string(), &0));
    /// ```
    pub fn insert_left(&mut self, left: L, right: &R) -> Option<L> {
        let r_hash = make_hash::<R, S>(&self.hash_builder, right);
        let right_item = self
            .right_set
            .get_mut(r_hash, equivalent_key_right(right))?;
        let right_id = right_item.id;
        let l_hash = make_hash::<L, S>(&self.hash_builder, &left);
        right_item.pairs.insert((l_hash, self.left_counter));
        let digest = self.remove_left(&left);
        let left_item = LeftItem {
            value: left,
            hash: r_hash,
            id: self.left_counter,
            r_id: right_id,
        };
        self.left_counter += 1;
        self.left_set.insert(
            l_hash,
            left_item,
            make_hasher::<LeftItem<L>, S>(&self.hash_builder),
        );
        digest
    }

    /// Adds an item to the left set of the map.
    ///
    /// Should this item be equal to another, the old item and everything it is paired
    /// with are removed and returned.
    ///
    /// Note: If you want to swap right item, use the [`swap_right`] or [`swap_right_remove`]
    /// method.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    ///
    /// let mut map: GroupMap<u64, String> = (0..5).map(|i| (i, "X".to_string())).collect();
    ///
    /// // Add a new right item to pair with future left items
    /// let op = map.insert_right(0.to_string());
    /// assert!(op.is_none());
    ///
    /// // Re-add an existing right item, removing the old copy and its paired left items
    /// let op = map.insert_right("X".to_string());
    /// assert_eq!(op, Some(((0..5).collect(),"X".to_string())));
    /// ```
    ///
    /// [`swap_right`]: #method.swap_right
    /// [`swap_right_remove`]: #method.swap_right_remove
    pub fn insert_right(&mut self, right: R) -> Option<(HashSet<L>, R)> {
        let digest = self.remove_right(&right);
        let r_hash = make_hash::<R, S>(&self.hash_builder, &right);
        let right_item = RightItem {
            value: right,
            pairs: HashSet::new(),
            id: self.right_counter,
        };
        self.right_counter += 1;
        self.right_set.insert(
            r_hash,
            right_item,
            make_hasher::<RightItem<R>, S>(&self.hash_builder),
        );
        digest
    }

    /// Inserts the given `new` right item and repairs all items paired with the `old` item but
    /// keeps the `old` item in the map.
    ///
    /// Note: Use the [`swap_right_remove`] method to remove the `old` item.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    ///
    /// let mut map = GroupMap::new();
    /// map.insert(1, "1");
    /// map.insert_left(2, &"1");
    /// map.swap_right(&"1", "2");
    ///
    /// assert!(map.contains_right(&"1"));
    /// assert!(!map.is_right_paired(&"1"));
    /// assert!(map.are_paired(&1, &"2"));
    /// assert!(map.are_paired(&2, &"2"));
    /// ```
    ///
    /// [`swap_right_remove`]: #method.swap_right_remove
    pub fn swap_right(&mut self, old: &R, new: R) {
        let old_hash = make_hash::<R, S>(&self.hash_builder, old);
        match self.right_set.get_mut(old_hash, equivalent_key_right(old)) {
            None => {
                self.insert_right(new);
            }
            Some(r) => {
                let set: HashSet<(u64, ID)> = r.pairs.drain().collect();
                let new_hash = make_hash::<R, S>(&self.hash_builder, &new);
                let item = RightItem {
                    value: new,
                    pairs: set.clone(),
                    id: self.right_counter,
                };
                self.right_set
                    .insert(new_hash, item, make_hasher(&self.hash_builder));
                self.right_counter += 1;
                for (hash, id) in set {
                    self.left_set
                        .get_mut(hash, left_with_left_id(id))
                        .unwrap()
                        .hash = new_hash;
                }
            }
        }
    }

    /// Inserts the given `new` right item, repairs all items paired with the `old` item, and
    /// return the `old` item.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    ///
    /// let mut map = GroupMap::new();
    /// map.insert(1, "1");
    /// map.insert_left(2, &"1");
    /// map.swap_right_remove(&"1", "2");
    ///
    /// assert!(!map.contains_right(&"1"));
    /// assert!(map.are_paired(&1, &"2"));
    /// assert!(map.are_paired(&2, &"2"));
    /// ```
    pub fn swap_right_remove(&mut self, old: &R, new: R) -> Option<R> {
        let old_hash = make_hash::<R, S>(&self.hash_builder, old);
        match self
            .right_set
            .remove_entry(old_hash, equivalent_key_right(old))
        {
            None => {
                self.insert_right(new);
                None
            }
            Some(mut r) => {
                let set: HashSet<(u64, ID)> = r.pairs.drain().collect();
                let new_hash = make_hash::<R, S>(&self.hash_builder, &new);
                let item = RightItem {
                    value: new,
                    pairs: set.clone(),
                    id: self.right_counter,
                };
                self.right_set
                    .insert(new_hash, item, make_hasher(&self.hash_builder));
                self.right_counter += 1;
                for (hash, id) in set {
                    self.left_set
                        .get_mut(hash, left_with_left_id(id))
                        .unwrap()
                        .hash = new_hash;
                }
                Some(r.value)
            }
        }
    }

    /// Pairs two existing items in the map. Returns `true` if they were successfully paired.
    /// Returns `false` if either item can not be found.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    ///
    /// let mut map = GroupMap::new();
    /// map.insert(1, "1");
    /// map.insert_right("2");
    ///
    /// assert!(map.pair(&1, &"2"));
    /// assert!(map.are_paired(&1, &"2"));
    /// assert!(!map.are_paired(&1, &"1"));
    /// ```
    pub fn pair(&mut self, left: &L, right: &R) -> bool {
        let l_hash = make_hash::<L, S>(&self.hash_builder, left);
        let r_hash = make_hash::<R, S>(&self.hash_builder, right);
        let opt_left = self.left_set.get_mut(l_hash, equivalent_key_left(left));
        let opt_right = self.right_set.get(r_hash, equivalent_key_right(right));
        let (digest, to_remove) = match (opt_left, opt_right) {
            (Some(left), Some(r)) => {
                let to_remove = Some((left.hash, left.r_id, left.id));
                left.hash = r_hash;
                left.r_id = r.id;
                (true, to_remove)
            }
            _ => (false, None),
        };
        // The specified right item is updated here to avoid potential collision should hash ==
        // r_hash
        if let Some(triple) = to_remove {
            let old_right = self
                .right_set
                .get_mut(triple.0, right_with_right_id(triple.1))
                .unwrap();
            old_right.pairs.remove(&(l_hash, triple.2));
            let new_right = self
                .right_set
                .get_mut(r_hash, equivalent_key_right(right))
                .unwrap();
            new_right.pairs.insert((l_hash, triple.2));
        }
        digest
    }

    /// Returns `false` if the item isn't found or is unpaired. Returns `true` otherwise.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    ///
    /// let mut map = GroupMap::new();
    /// map.insert(1, "1");
    /// map.insert_right("2");
    /// assert!(map.is_right_paired(&"1"));
    /// assert!(!map.is_right_paired(&"2"));
    /// ```
    pub fn is_right_paired(&self, right: &R) -> bool {
        let r_hash = make_hash::<R, S>(&self.hash_builder, right);
        let opt_right = self.right_set.get(r_hash, equivalent_key_right(right));
        match opt_right {
            Some(r) => !r.pairs.is_empty(),
            None => false,
        }
    }

    /// Returns `true` if both items are in the map and are paired together; otherwise, returns
    /// `false`.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    ///
    /// let mut map = GroupMap::new();
    /// map.insert(1, "1");
    /// assert!(map.are_paired(&1, &"1"));
    /// ```
    pub fn are_paired(&self, left: &L, right: &R) -> bool {
        let l_hash = make_hash::<L, S>(&self.hash_builder, left);
        let r_hash = make_hash::<R, S>(&self.hash_builder, right);
        let opt_left = self.left_set.get(l_hash, equivalent_key_left(left));
        let opt_right = self.right_set.get(r_hash, equivalent_key_right(right));
        match (opt_left, opt_right) {
            (Some(left), Some(right)) => {
                left.hash == r_hash && right.pairs.contains(&(l_hash, left.id))
            }
            _ => false,
        }
    }

    /// Returns `true` if the item is found and `false` otherwise.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    ///
    /// let mut map = GroupMap::new();
    /// map.insert(1, "1");
    /// assert!(map.contains_left(&1));
    /// assert!(!map.contains_left(&2));
    /// ```
    pub fn contains_left(&self, left: &L) -> bool {
        let hash = make_hash::<L, S>(&self.hash_builder, left);
        self.left_set.get(hash, equivalent_key_left(left)).is_some()
    }

    /// Returns `true` if the item is found and `false` otherwise.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    ///
    /// let mut map = GroupMap::new();
    /// map.insert(1, "1");
    /// map.insert_right("2");
    /// assert!(map.contains_right(&"1"));
    /// assert!(map.contains_right(&"2"));
    /// assert!(!map.contains_right(&"3"));
    /// ```
    pub fn contains_right(&self, right: &R) -> bool {
        let hash = make_hash::<R, S>(&self.hash_builder, right);
        self.right_set
            .get(hash, equivalent_key_right(right))
            .is_some()
    }

    /// Removes a pair of items only if they are paired together. The right item and every item it
    /// was paired with are returned.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    ///
    /// let mut map = GroupMap::new();
    /// map.insert(1, "1");
    /// map.insert_left(2, &"1");
    /// assert_eq!(map.remove(&1, &"1"), Some(((1..3).collect(), "1")));
    /// assert_eq!(map.remove(&1, &"1"), None);
    /// ```
    pub fn remove(&mut self, left: &L, right: &R) -> Option<(HashSet<L>, R)> {
        if self.are_paired(left, right) {
            self.remove_right(right)
        } else {
            None
        }
    }

    /// Removes the given `left` item from the left set and returns it.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    ///
    /// let mut map = GroupMap::new();
    /// map.insert(1, "1");
    /// assert_eq!(map.remove_left(&1), Some(1));
    /// assert_eq!(map.remove_left(&2), None);
    /// ```
    pub fn remove_left(&mut self, item: &L) -> Option<L> {
        let l_hash = make_hash::<L, S>(&self.hash_builder, item);
        let left_item = self
            .left_set
            .remove_entry(l_hash, equivalent_key_left(item))?;
        let pair = (l_hash, left_item.id);
        self.right_set
            .get_mut(left_item.hash, right_with_left_pair(&pair))
            .unwrap()
            .pairs
            .remove(&pair);
        Some(left_item.extract())
    }

    /// Removes the given `right` item from the right set and returns it and all of its paired left
    /// items.
    ///
    /// # Examples
    /// ```rust
    /// # use hashbrown::HashSet;
    /// use cycle_map::GroupMap;
    ///
    /// let mut map = GroupMap::new();
    /// map.insert(1, "1");
    /// map.insert_left(2, &"1");
    /// map.insert_right("2");
    /// assert_eq!(map.remove_right(&"1"), Some(((1..3).collect(), "1")));
    /// assert_eq!(map.remove_right(&"2"), Some((HashSet::new(), "2")));
    /// ```
    pub fn remove_right(&mut self, item: &R) -> Option<(HashSet<L>, R)> {
        let r_hash = make_hash::<R, S>(&self.hash_builder, item);
        let right_item = self
            .right_set
            .remove_entry(r_hash, equivalent_key_right(item))?;
        let left_vec: HashSet<L> = right_item
            .pairs
            .iter()
            .map(|(h, i)| {
                self.left_set
                    .remove_entry(*h, left_with_left_id(*i))
                    .unwrap()
                    .extract()
            })
            .collect();
        Some((left_vec, right_item.extract()))
    }

    /// Removes a pair using the hash of the left item, right item, and their shared pairing id
    fn remove_via_hash_and_id(&mut self, r_hash: u64, id: ID) -> Option<(Vec<L>, R)> {
        let right = self
            .right_set
            .remove_entry(r_hash, right_with_right_id(id))?;
        let left_vec = right
            .pairs
            .iter()
            .map(|(h, i)| {
                self.left_set
                    .remove_entry(*h, left_with_left_id(*i))
                    .unwrap()
                    .extract()
            })
            .collect();
        Some((left_vec, right.extract()))
    }

    /// Returns an iterator over items in the left set that are paired with the given item.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    /// let mut map = GroupMap::new();
    /// map.insert(1, "1");
    /// map.insert_left(2, &"1");
    /// let mut iter = map.get_left_iter(&"1").unwrap();
    /// // The iterator visits items in an arbitary order
    /// let val = iter.next().unwrap();
    /// assert!(*val == 1 || *val == 2);
    /// let val = iter.next().unwrap();
    /// assert!(*val == 1 || *val == 2);
    /// assert!(iter.next().is_none());
    /// ```
    pub fn get_left_iter<Q>(&self, item: &Q) -> Option<PairIter<'_, L, R, S>>
    where
        R: Borrow<Q>,
        Q: Hash + Eq,
    {
        let r_hash = make_hash::<_, S>(&self.hash_builder, item);
        let right_item: &RightItem<R> = self.right_set.get(r_hash, equivalent_key_right(item))?;
        Some(PairIter {
            iter: right_item.pairs.iter(),
            map_ref: self,
            marker: PhantomData,
        })
    }

    /// Gets a reference to an item in the left set using an item in the right set.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    /// let mut map = GroupMap::new();
    /// map.insert(1, "1");
    /// map.insert_right("2");
    /// assert_eq!(map.get_right(&1), Some(&"1"));
    /// assert_eq!(map.get_right(&2), None);
    /// ```
    pub fn get_right<Q>(&self, item: &Q) -> Option<&R>
    where
        L: Borrow<Q>,
        Q: Hash + Eq,
    {
        let l_hash = make_hash::<_, S>(&self.hash_builder, item);
        let left_item = self.get_left_inner_with_hash(item, l_hash)?;
        match self
            .right_set
            .get(left_item.hash, right_with_right_id(left_item.r_id))
        {
            None => None,
            Some(pairing) => Some(&pairing.value),
        }
    }

    #[inline]
    fn get_left_inner_with_hash<Q>(&self, item: &Q, hash: u64) -> Option<&LeftItem<L>>
    where
        L: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.left_set.get(hash, equivalent_key_left(item))
    }

    #[inline]
    fn get_right_inner_with_hash<Q>(&self, item: &Q, hash: u64) -> Option<&RightItem<R>>
    where
        R: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.right_set.get(hash, equivalent_key_right(item))
    }

    /// Returns an iterator that visits all the items in the map in an arbitary order.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    ///
    /// let mut map: GroupMap<String, u64> = (0..5).map(|i| (i.to_string(), i)).collect();
    /// map.insert_right(5);
    ///
    /// for (left, right) in map.iter() {
    ///     if let Some(l) = left {
    ///         assert!(*right != 5);
    ///     } else {
    ///         assert_eq!(*right, 5);
    ///     }
    ///     println!("left: {left:?}, right: {right}");
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, L, R, S> {
        Iter {
            right_iter: unsafe { self.right_set.iter() },
            left_iter: None,
            map_ref: self,
        }
    }

    /// Returns an iterator that visits all the pairs in the map in an arbitary order.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    ///
    /// let mut map: GroupMap<String, u64> = (0..5).map(|i| (i.to_string(), i)).collect();
    /// map.insert_right(5);
    ///
    /// for (left, right) in map.iter_paired() {
    ///     assert!(*right != 5);
    ///     println!("left: {left}, right: {right}");
    /// }
    /// ```
    pub fn iter_paired(&self) -> PairedIter<'_, L, R, S> {
        PairedIter {
            left_iter: unsafe { self.left_set.iter() },
            map_ref: self,
        }
    }

    /// Returns an iterator that visits all the pairs in the map in an arbitary order.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    ///
    /// let mut map: GroupMap<String, u64> = (0..5).map(|i| (i.to_string(), i)).collect();
    /// map.insert_right(5);
    ///
    /// let mut iter = map.iter_unpaired();
    ///
    /// assert_eq!(iter.next(), Some(&5));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter_unpaired(&self) -> UnpairedIter<'_, L, R, S> {
        UnpairedIter {
            right_iter: unsafe { self.right_set.iter() },
            map_ref: self,
        }
    }

    /// Returns an iterator that visits all left items in an arbitary order.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    ///
    /// let mut map: GroupMap<String, u64> = (0..5).map(|i| (i.to_string(), i)).collect();
    /// map.insert_right(5);
    ///
    /// for left in map.iter_left() {
    ///     println!("left: {left}");
    /// }
    /// ```
    pub fn iter_left(&self) -> LeftIter<'_, L> {
        LeftIter {
            left_iter: unsafe { self.left_set.iter() },
            marker: PhantomData,
        }
    }

    /// Returns an iterator that visits all right items in an arbitary order.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    ///
    /// let mut map: GroupMap<String, u64> = (0..5).map(|i| (i.to_string(), i)).collect();
    /// map.insert_right(5);
    ///
    /// for right in map.iter_right() {
    ///     println!("right: {right}");
    /// }
    /// ```
    pub fn iter_right(&self) -> RightIter<'_, R> {
        RightIter {
            right_iter: unsafe { self.right_set.iter() },
            marker: PhantomData,
        }
    }

    /// Visits all pairs in the map and drops all left items if the pair causes the
    /// given closure to return `false`. Pairs are visited in an arbitary order.
    ///
    /// Note: Only left items are dropped as dropping a right item would cause an entire collection
    /// of left items to be dropped.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    ///
    /// let mut map: GroupMap<String, u64> = (0..50).map(|i| (i.to_string(), i)).collect();
    /// map.extend((50..100).map(|i| (None, i)));
    ///
    /// //Remove all left items with an odd right item
    /// map.retain_unpaired(|r| r % 2 == 0);
    /// assert_eq!(map.len_left(), 50);
    /// assert_eq!(map.len_right(), 75);
    /// ```
    pub fn retain_paired<F>(&mut self, mut f: F)
    where
        F: FnMut(&L, &R) -> bool,
    {
        // right hash, left id
        let mut to_drop: Vec<(u64, ID)> = Vec::with_capacity(self.left_set.len());
        for (l, r) in self.iter_paired() {
            if f(l, r) {
                let l_hash = make_hash(&self.hash_builder, l);
                let l_item = self.get_left_inner_with_hash(l, l_hash).unwrap();
                to_drop.push((l_hash, l_item.id));
            }
        }
        for (l_hash, id) in to_drop {
            self.left_set.remove_entry(l_hash, left_with_left_id(id));
        }
    }

    /// Visits all unpaired right items in the map and drops all items if the item causes the given
    /// closure to return `false`. Items are visited in an arbitary order.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    ///
    /// let mut map: GroupMap<String, u64> = (0..50).map(|i| (i.to_string(), i)).collect();
    /// map.extend((50..100).map(|i| (None, i)));
    ///
    /// //Remove all left items with an odd right item
    /// map.retain_paired(|_, r| r % 2 == 0);
    /// assert_eq!(map.len_left(), 25);
    /// assert_eq!(map.len_right(), 100);
    /// ```
    pub fn retain_unpaired<F>(&mut self, mut f: F)
    where
        F: FnMut(&R) -> bool,
    {
        // right hash, left id
        let mut to_drop: Vec<(u64, ID)> = Vec::with_capacity(self.left_set.len());
        for r in self.iter_unpaired() {
            if f(r) {
                let r_hash = make_hash::<R, S>(&self.hash_builder, r);
                let r_item = self.get_right_inner_with_hash(r, r_hash).unwrap();
                to_drop.push((r_hash, r_item.id));
            }
        }
        for (r_hash, id) in to_drop {
            self.remove_via_hash_and_id(r_hash, id);
        }
    }
}

impl<L, R, S> Clone for GroupMap<L, R, S>
where
    L: Eq + Hash + Clone,
    R: Eq + Hash + Clone,
    S: BuildHasher + Clone,
{
    fn clone(&self) -> Self {
        Self {
            left_set: self.left_set.clone(),
            right_set: self.right_set.clone(),
            left_counter: self.left_counter,
            right_counter: self.right_counter,
            hash_builder: self.hash_builder.clone(),
        }
    }
}

impl<L, R, S> Default for GroupMap<L, R, S>
where
    S: Default,
{
    fn default() -> Self {
        Self::with_hasher(Default::default())
    }
}

impl<L, R, S> fmt::Debug for GroupMap<L, R, S>
where
    L: Hash + Eq + fmt::Debug,
    R: Hash + Eq + fmt::Debug,
    S: BuildHasher,
{
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_set().entries(self.iter()).finish()
    }
}

impl<L, R, S> PartialEq<GroupMap<L, R, S>> for GroupMap<L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
    fn eq(&self, other: &Self) -> bool {
        if self.len_left() != other.len_left() && self.len_right() != other.len_right() {
            return false;
        }
        self.iter().all(|(l_opt, r)| match l_opt {
            Some(l) => other.are_paired(l, r),
            None => !other.is_right_paired(r),
        })
    }
}

impl<L, R, S> Eq for GroupMap<L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
}

impl<L, R, S> GroupMap<L, R, S> {
    /// Creates a `GroupMap`and that uses the given hasher.
    ///
    /// Warning: `hash_builder` is normally randomly generated, and is designed to allow
    /// `GroupMap`s to be resistant to attacks that cause many collisions and very poor
    /// performance. Setting it manually using this function can expose a DoS attack vector.
    ///
    /// The `hash_builder` passed should implement the [`BuildHasher`] trait for the GroupMap to be
    /// useful, see its documentation for details.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    /// use std::collections::hash_map::RandomState;
    ///
    /// let s = RandomState::new();
    /// let mut map = GroupMap::with_capacity_and_hasher(10, s);
    /// map.insert(1, "1");
    /// ```
    pub const fn with_hasher(hash_builder: S) -> Self {
        Self {
            hash_builder,
            left_counter: ID(0),
            right_counter: ID(0),
            left_set: RawTable::new(),
            right_set: RawTable::new(),
        }
    }

    /// Creates a `GroupMap` with inner sets that have at least the specified capacity, and that
    /// uses the given hasher.
    ///
    /// The map will be able to hold at least `capacity` many pairs before reallocating.
    ///
    /// Warning: `hash_builder` is normally randomly generated, and is designed to allow
    /// `GroupMap`s to be resistant to attacks that cause many collisions and very poor
    /// performance. Setting it manually using this function can expose a DoS attack vector.
    ///
    /// The `hash_builder` passed should implement the [`BuildHasher`] trait for the GroupMap to be
    /// useful, see its documentation for details.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    /// use std::collections::hash_map::RandomState;
    ///
    /// let s = RandomState::new();
    /// let mut map = GroupMap::with_capacity_and_hasher(10, s);
    /// map.insert(1, "1");
    /// ```
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        Self {
            hash_builder,
            left_counter: ID(0),
            right_counter: ID(0),
            left_set: RawTable::with_capacity(capacity),
            right_set: RawTable::with_capacity(capacity),
        }
    }

    /// Returns a reference to the [`BuildHasher`] used by the map
    pub fn hasher(&self) -> &S {
        &self.hash_builder
    }

    /// Returns the number of items that the left set can hold without reallocation.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    /// let map: GroupMap<u64, String> = GroupMap::with_capacity(100);
    /// assert!(map.capacity_left() >= 100);
    /// ```
    pub fn capacity_left(&self) -> usize {
        // The size of the sets is always equal
        self.left_set.capacity()
    }

    /// Returns the number of items that the right set can hold without reallocation.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    /// let map: GroupMap<u64, String> = GroupMap::with_capacity(100);
    /// assert!(map.capacity_right() >= 100);
    /// ```
    pub fn capacity_right(&self) -> usize {
        // The size of the sets is always equal
        self.right_set.capacity()
    }

    /// Returns the number of items in the left set.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    ///
    /// let mut map = GroupMap::new();
    /// assert_eq!(map.len_left(), 0);
    /// map.insert(1, "1");
    /// map.insert_right("2");
    /// assert_eq!(map.len_left(), 1);
    /// ```
    pub fn len_left(&self) -> usize {
        self.left_set.len()
    }

    /// Returns the number of items in the right set.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    ///
    /// let mut map = GroupMap::new();
    /// assert_eq!(map.len_right(), 0);
    /// map.insert(1, "1");
    /// map.insert_right("2");
    /// assert_eq!(map.len_right(), 2);
    /// ```
    pub fn len_right(&self) -> usize {
        self.right_set.len()
    }

    /// Returns `true` if no items are in the map and `false` otherwise.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    ///
    /// let mut map = GroupMap::new();
    /// assert!(map.is_empty());
    /// map.insert(1, "1");
    /// assert!(!map.is_empty());
    ///
    /// let mut map: GroupMap<u64, &str> = GroupMap::new();
    /// assert!(map.is_empty());
    /// map.insert_right("1");
    /// assert_eq!(map.len_left(), 0);
    /// assert_eq!(map.len_right(), 1);
    /// assert!(!map.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len_left() + self.len_right() == 0
    }

    /// Removes all items for the map while keeping the backing memory allocated for reuse.
    ///
    /// # Examples
    /// ```rust
    /// use cycle_map::GroupMap;
    ///
    /// let mut map = GroupMap::new();
    /// assert!(map.is_empty());
    /// map.insert(1, "a");
    /// assert!(!map.is_empty());
    /// map.clear();
    /// assert!(map.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.left_set.clear();
        self.right_set.clear();
    }
}

impl<L, R, S> Extend<(Option<L>, R)> for GroupMap<L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
    #[inline]
    fn extend<T: IntoIterator<Item = (Option<L>, R)>>(&mut self, iter: T) {
        for (left, right) in iter {
            if let Some(l) = left {
                self.insert(l, right);
            } else {
                self.insert_right(right);
            }
        }
    }
}

impl<L, R, S> Extend<(L, R)> for GroupMap<L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
    #[inline]
    fn extend<T: IntoIterator<Item = (L, R)>>(&mut self, iter: T) {
        for (left, right) in iter {
            self.insert(left, right);
        }
    }
}

impl<L, R> FromIterator<(Option<L>, R)> for GroupMap<L, R>
where
    L: Hash + Eq,
    R: Hash + Eq,
{
    fn from_iter<T: IntoIterator<Item = (Option<L>, R)>>(iter: T) -> Self {
        let mut digest = GroupMap::default();
        digest.extend(iter);
        digest
    }
}

impl<L, R> FromIterator<(L, R)> for GroupMap<L, R>
where
    L: Hash + Eq,
    R: Hash + Eq,
{
    fn from_iter<T: IntoIterator<Item = (L, R)>>(iter: T) -> Self {
        let mut digest = GroupMap::default();
        digest.extend(iter);
        digest
    }
}

/// An iterator over the entry items of a `GroupMap`.
pub struct Iter<'a, L, R, S> {
    right_iter: RawIter<RightItem<R>>,
    left_iter: Option<hash_set::Iter<'a, (u64, ID)>>,
    map_ref: &'a GroupMap<L, R, S>,
}

impl<L, R, S> Clone for Iter<'_, L, R, S> {
    fn clone(&self) -> Self {
        Self {
            right_iter: self.right_iter.clone(),
            left_iter: None,
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
    type Item = (Option<&'a L>, &'a R);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(iter) = self.left_iter.as_mut() {
            if let Some(pair) = iter.next() {
                let left = self
                    .map_ref
                    .left_set
                    .get(pair.0, left_with_left_id(pair.1))
                    .unwrap();
                let right = self
                    .map_ref
                    .right_set
                    .get(left.hash, right_with_right_id(left.r_id))
                    .unwrap();
                return Some((Some(&left.value), &right.value));
            }
        }
        match self.right_iter.next() {
            Some(r) => {
                let r_ref = unsafe { &r.as_ref() };
                if r_ref.pairs.is_empty() {
                    Some((None, &r_ref.value))
                } else {
                    let mut iter = r_ref.pairs.iter();
                    let pair = iter.next().unwrap();
                    self.left_iter = Some(iter);
                    let left = self
                        .map_ref
                        .left_set
                        .get(pair.0, left_with_left_id(pair.1))
                        .map(|o| &o.value);
                    Some((left, &r_ref.value))
                }
            }
            None => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.right_iter.size_hint()
    }
}

impl<'a, L, R, S> ExactSizeIterator for Iter<'a, L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
    fn len(&self) -> usize {
        self.clone().count()
    }
}

impl<L, R, S> FusedIterator for Iter<'_, L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
}

/// An iterator over the entry pairs of a `GroupMap`.
pub struct PairedIter<'a, L, R, S> {
    left_iter: RawIter<LeftItem<L>>,
    map_ref: &'a GroupMap<L, R, S>,
}

impl<L, R, S> Clone for PairedIter<'_, L, R, S> {
    fn clone(&self) -> Self {
        Self {
            left_iter: self.left_iter.clone(),
            map_ref: self.map_ref,
        }
    }
}

impl<L, R, S> fmt::Debug for PairedIter<'_, L, R, S>
where
    L: Hash + Eq + fmt::Debug,
    R: Hash + Eq + fmt::Debug,
    S: BuildHasher,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, L, R, S> Iterator for PairedIter<'a, L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
    type Item = (&'a L, &'a R);

    fn next(&mut self) -> Option<Self::Item> {
        match self.left_iter.next() {
            Some(l_bucket) => {
                let l_item = unsafe { l_bucket.as_ref() };
                let r_item = self
                    .map_ref
                    .right_set
                    .get(l_item.hash, right_with_right_id(l_item.r_id))
                    .unwrap();
                Some((&l_item.value, &r_item.value))
            }
            None => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.left_iter.size_hint()
    }
}

impl<'a, L, R, S> ExactSizeIterator for PairedIter<'a, L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
    fn len(&self) -> usize {
        self.clone().count()
    }
}

impl<L, R, S> FusedIterator for PairedIter<'_, L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
}

/// An iterator over the entry pairs of a `GroupMap`.
pub struct UnpairedIter<'a, L, R, S> {
    right_iter: RawIter<RightItem<R>>,
    map_ref: &'a GroupMap<L, R, S>,
}

impl<L, R, S> Clone for UnpairedIter<'_, L, R, S> {
    fn clone(&self) -> Self {
        Self {
            right_iter: self.right_iter.clone(),
            map_ref: self.map_ref,
        }
    }
}

impl<L, R, S> fmt::Debug for UnpairedIter<'_, L, R, S>
where
    L: Hash + Eq + fmt::Debug,
    R: Hash + Eq + fmt::Debug,
    S: BuildHasher,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, L, R, S> Iterator for UnpairedIter<'a, L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
    type Item = &'a R;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(item) = self.right_iter.next().map(|r| unsafe { r.as_ref() }) {
            if item.pairs.is_empty() {
                return Some(&item.value);
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.right_iter.size_hint()
    }
}

impl<'a, L, R, S> ExactSizeIterator for UnpairedIter<'a, L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
    fn len(&self) -> usize {
        self.clone().count()
    }
}

impl<L, R, S> FusedIterator for UnpairedIter<'_, L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
}

/// An iterator over the elements of an inner set of a `GroupMap`.
pub struct LeftIter<'a, L> {
    left_iter: RawIter<LeftItem<L>>,
    marker: PhantomData<&'a L>,
}

impl<L> Clone for LeftIter<'_, L> {
    fn clone(&self) -> Self {
        Self {
            left_iter: self.left_iter.clone(),
            marker: PhantomData,
        }
    }
}

impl<L> fmt::Debug for LeftIter<'_, L>
where
    L: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, L> Iterator for LeftIter<'a, L> {
    type Item = &'a L;

    fn next(&mut self) -> Option<Self::Item> {
        self.left_iter.next().map(|b| unsafe { &b.as_ref().value })
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.left_iter.size_hint()
    }
}

impl<L> ExactSizeIterator for LeftIter<'_, L> {
    fn len(&self) -> usize {
        self.left_iter.len()
    }
}

impl<L> FusedIterator for LeftIter<'_, L> {}

/// An iterator over the elements of an inner set of a `GroupMap`.
pub struct RightIter<'a, R> {
    right_iter: RawIter<RightItem<R>>,
    marker: PhantomData<&'a R>,
}

impl<R> Clone for RightIter<'_, R> {
    fn clone(&self) -> Self {
        Self {
            right_iter: self.right_iter.clone(),
            marker: PhantomData,
        }
    }
}

impl<R> fmt::Debug for RightIter<'_, R>
where
    R: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, R> Iterator for RightIter<'a, R> {
    type Item = &'a R;

    fn next(&mut self) -> Option<Self::Item> {
        self.right_iter.next().map(|b| unsafe { &b.as_ref().value })
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.right_iter.size_hint()
    }
}

impl<R> ExactSizeIterator for RightIter<'_, R> {
    fn len(&self) -> usize {
        self.right_iter.len()
    }
}

impl<R> FusedIterator for RightIter<'_, R> {}

/// An iterator over the elements of an inner set of a `GroupMap`.
pub struct PairIter<'a, L, R, S> {
    iter: hash_set::Iter<'a, (u64, ID)>,
    map_ref: &'a GroupMap<L, R, S>,
    marker: PhantomData<&'a L>,
}

impl<L, R, S> Clone for PairIter<'_, L, R, S> {
    fn clone(&self) -> Self {
        Self {
            iter: self.iter.clone(),
            map_ref: self.map_ref,
            marker: PhantomData,
        }
    }
}

impl<L, R, S> fmt::Debug for PairIter<'_, L, R, S>
where
    L: Eq + fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, L, R, S> Iterator for PairIter<'a, L, R, S>
where
    L: Eq,
{
    type Item = &'a L;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|(hash, id)| {
            &self
                .map_ref
                .left_set
                .get(*hash, left_with_left_id(*id))
                .unwrap()
                .value
        })
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<L, R, S> ExactSizeIterator for PairIter<'_, L, R, S>
where
    L: Eq,
{
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<L: Eq, R, S> FusedIterator for PairIter<'_, L, R, S> {}

impl<T> LeftItem<T> {
    // Consumes the pair and returns the held `T`
    pub(crate) fn extract(self) -> T {
        self.value
    }
}

impl<T: Hash> Hash for LeftItem<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value.hash(state)
    }
}

impl<T: PartialEq> PartialEq for LeftItem<T> {
    fn eq(&self, other: &Self) -> bool {
        self.id.eq(&other.id) && self.value.eq(&other.value)
    }
}

impl<T> Eq for LeftItem<T> where T: Hash + Eq {}

impl<T: Clone> Clone for LeftItem<T> {
    fn clone(&self) -> Self {
        Self {
            value: self.value.clone(),
            hash: self.hash,
            r_id: self.r_id,
            id: self.id,
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for LeftItem<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "LeftItem {{ value: {:?}, hash: {}, id: {} }}",
            self.value, self.hash, self.id.0
        )
    }
}

impl<T> RightItem<T> {
    // Consumes the pair and returns the held `T`
    pub(crate) fn extract(self) -> T {
        self.value
    }
}

impl<T: Hash> Hash for RightItem<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value.hash(state)
    }
}

impl<T: PartialEq> PartialEq for RightItem<T> {
    fn eq(&self, other: &Self) -> bool {
        self.id.eq(&other.id) && self.value.eq(&other.value)
    }
}

impl<T: Eq> Eq for RightItem<T> {}

impl<T: Clone> Clone for RightItem<T> {
    fn clone(&self) -> Self {
        Self {
            value: self.value.clone(),
            pairs: self.pairs.clone(),
            id: self.id,
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for RightItem<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "RightItem {{ value: {:?}, id: {}, pairs: {:?} }}",
            self.value, self.id.0, self.pairs
        )
    }
}

impl AddAssign<u64> for ID {
    fn add_assign(&mut self, other: u64) {
        self.0 += other;
    }
}
