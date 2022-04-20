use std::{
    default::Default,
    fmt,
    hash::{BuildHasher, Hash},
    iter::FusedIterator,
    marker::PhantomData,
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

pub(crate) fn equivalent_key<T: PartialEq<Q>, Q: PartialEq + ?Sized>(
    k: &Q,
) -> impl Fn(&T) -> bool + '_ {
    move |x| x.eq(k)
}

pub(crate) fn left_hash_and_id<T: PartialEq + ?Sized>(
    hash: u64,
    id: u64,
) -> impl Fn(&LeftItem<T>) -> bool {
    move |x| x.id == id && x.hash == hash
}

pub(crate) fn right_hash_and_id<'a, T: PartialEq + ?Sized>(
    pair: &'a (u64, u64),
) -> impl Fn(&RightItem<T>) -> bool + 'a {
    move |x| x.pairs.contains(pair)
}

pub(crate) fn left_just_id<'a, T: PartialEq + ?Sized>(
    id: u64,
) -> impl Fn(&LeftItem<T>) -> bool + 'a {
    move |x| x.id == id
}

pub(crate) fn right_just_id<'a, T: PartialEq + ?Sized>(
    id: u64,
) -> impl Fn(&RightItem<T>) -> bool + 'a {
    move |x| x.id == id
}

// Contains a value and the hash of the item that the value maps to.
pub(crate) struct LeftItem<T> {
    pub(crate) value: T,
    pub(crate) hash: u64,
    pub(crate) id: u64,
}

// Contains a value and the hash of the item that the value maps to.
pub(crate) struct RightItem<T> {
    pub(crate) value: T,
    pub(crate) pairs: HashSet<(u64, u64)>, // Contains (hash, id) of pair items
    pub(crate) id: u64, // Right items don't have to be paired, so an id is needed
}

/// A hash map implementation that allows bi-directional, near-constant time lookups.
///
/// Unlike `CycleMap` which bijectively maps two sets together, a `GroupMap` weakly
/// [`surjectively`] maps two sets together. In other words, every item in the left set much be
/// paired to an item in the right set, but two left items are allowed to map to the same right
/// item. However, the "weak" surjectivity comes from the fact that not all right items have to be
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
    pub(crate) counter: u64,
    left_set: RawTable<LeftItem<L>>,
    right_set: RawTable<RightItem<R>>,
}

impl<L, R> GroupMap<L, R, DefaultHashBuilder> {
    #[inline]
    /// Creates a new GroupMap
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    /// Creates a new GroupMap whose inner sets each of the given capacity
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
    /// Inserts the given pair. If left is already in the left set, it is remapped to the givrn
    /// right item. Similarly, if right is in the right set, the left item is added to left set and
    /// paired with right. If both items are already in the map, they are similar paired.
    pub fn insert(&mut self, left: L, right: R) {
        let l_hash = make_hash::<L, S>(&self.hash_builder, &left);
        let r_hash = make_hash::<R, S>(&self.hash_builder, &right);
        let opt_left = self.left_set.get_mut(l_hash, equivalent_key(&left));
        let opt_right = self.right_set.get_mut(r_hash, equivalent_key(&right));
        match (opt_left, opt_right) {
            (None, None) => {
                let left_item = LeftItem { value: left, hash: r_hash, id: self.counter };
                self.left_set.insert(l_hash, left_item, make_hasher(&self.hash_builder));
                let mut set = HashSet::with_capacity(1);
                set.insert((l_hash, self.counter));
                self.counter += 1;
                let right_item = RightItem { value: right, pairs: set, id: self.counter };
                self.right_set.insert(l_hash, right_item, make_hasher(&self.hash_builder));
                self.counter += 1;
            },
            (Some(l), None) => {
                l.hash = r_hash;
                let r = self.right_set.get_mut(r_hash, right_just_id(l.id)).unwrap();
                r.pairs.remove(&(l_hash, l.id));
                let mut set = HashSet::with_capacity(1);
                set.insert((l_hash, l.id));
                let right_item = RightItem { value: right, pairs: set, id: self.counter };
                self.right_set.insert(l_hash, right_item, make_hasher(&self.hash_builder));
                self.counter += 1;
            }
            (None, Some(r)) => {
                r.pairs.insert((l_hash, self.counter));
                let left_item = LeftItem { value: left, hash: r_hash, id: self.counter };
                self.left_set.insert(l_hash, left_item, make_hasher(&self.hash_builder));
                self.counter += 1;
            },
            (Some(l), Some(r)) => {
                r.pairs.insert((l_hash, l.id));
                let r = self.right_set.get_mut(l.hash, right_hash_and_id(&(l_hash, l.id))).unwrap();
                r.pairs.remove(&(l_hash, l.id));
                l.hash = r_hash;
            },
        }
    }

    /// Adds a pair of items to the map.
    ///
    /// Should the left element be equal to another left element, the old pair is removed and
    /// returned. The same goes for the right element.
    ///
    /// There is a chance for collision here. Collision occurs when the map contains elements with
    /// identical hashes as the given left and right elements, and they are paired to each other.
    /// In such a case, the old pair is returned and the new pair is inserted.
    /// 
    /// TODO: This should just pair thing in-place... Nothing should be removed
    pub fn insert_remove(&mut self, left: L, right: R) -> (Option<L>, Option<(Vec<L>, R)>) {
        let opt_from_left = self.remove_left(&left);
        let opt_from_right = self.remove_right(&right);
        let digest = (opt_from_left, opt_from_right);
        let l_hash = make_hash::<L, S>(&self.hash_builder, &left);
        let r_hash = make_hash::<R, S>(&self.hash_builder, &right);
        let left_item = LeftItem {
            value: left,
            hash: r_hash,
            id: self.counter,
        };
        let mut set = HashSet::with_capacity(1);
        set.insert((l_hash, self.counter));
        self.counter += 1;
        let right_item = RightItem {
            value: right,
            pairs: set,
            id: self.counter,
        };
        self.counter += 1;
        self.left_set.insert(
            l_hash,
            left_item,
            make_hasher::<LeftItem<L>, S>(&self.hash_builder),
        );
        self.right_set.insert(
            r_hash,
            right_item,
            make_hasher::<RightItem<R>, S>(&self.hash_builder),
        );
        digest
    }

    /// Adds an item to the left set of the map.
    ///
    /// Should this item be equal to another, the old item is removed. If that item was paired with
    /// a right item, the pair is removed.
    ///
    /// Note: If you want to swap the left item in a pair, use the [`swap_left`] method.
    ///
    /// [`swap_left`]: struct.GroupMap.html#method.swap_left
    pub fn insert_left(&mut self, left: L, right: &R) -> Option<L> {
        let r_hash = make_hash::<R, S>(&self.hash_builder, right);
        let right_item = self.right_set.get_mut(r_hash, equivalent_key(right))?;
        let l_hash = make_hash::<L, S>(&self.hash_builder, &left);
        right_item.pairs.insert((l_hash, self.counter));
        let digest = self.remove_left(&left);
        let left_item = LeftItem {
            value: left,
            hash: r_hash,
            id: self.counter,
        };
        self.counter += 1;
        self.left_set.insert(
            l_hash,
            left_item,
            make_hasher::<LeftItem<L>, S>(&self.hash_builder),
        );
        digest
    }

    /// Adds an item to the right set of the map.
    ///
    /// Should this item be equal to another, the old item is removed. If that item was paired with
    /// a left item, the pair is removed.
    ///
    /// Note: If you want to swap the right item in a pair, use the [`swap_right`] method.
    ///
    /// [`swap_right`]: struct.GroupMap.html#method.swap_right
    pub fn insert_right(&mut self, right: R) -> Option<(Vec<L>, R)> {
        let opt_from_right = self.remove_right(&right);
        let digest = opt_from_right;
        let r_hash = make_hash::<R, S>(&self.hash_builder, &right);
        let right_item = RightItem {
            value: right,
            pairs: HashSet::new(),
            id: self.counter,
        };
        self.counter += 1;
        self.right_set.insert(
            r_hash,
            right_item,
            make_hasher::<RightItem<R>, S>(&self.hash_builder),
        );
        digest
    }
    
    /// Inserts the given `new` right item and repairs all items paired with the `old` item with
    /// the `new` item.
    pub fn swap_right(&mut self, old: &R, new: R) {
        let old_hash = make_hash::<R, S>(&self.hash_builder, old);
        match self.right_set.get_mut(old_hash, equivalent_key(old)) {
            None => {
                self.insert_right(new);
            },
            Some(r) => {
                let set: HashSet<(u64, u64)> = r.pairs.drain().collect();
                let new_hash = make_hash::<R, S>(&self.hash_builder, &new);
                let item = RightItem { value: new, pairs: set.clone(), id: self.counter };
                self.right_set.insert(new_hash, item, make_hasher(&self.hash_builder));
                self.counter += 1;
                for (hash, id) in set {
                    self.left_set.get_mut(hash, left_just_id(id)).unwrap().hash = new_hash;
                }
            }
        }
    }
    
    /// Removes the given `old` right item, inserts the given `new` right item, and repairs all
    /// items paired with the `old` item with the `new` item.
    /// 
    /// If the `old` item isn't in the map, `None` is returned. Otherwise, the `old` value is
    /// returned.
    pub fn swap_right_remove(&mut self, old: &R, new: R) -> Option<R> {
        let old_hash = make_hash::<R, S>(&self.hash_builder, old);
        match self.right_set.remove_entry(old_hash, equivalent_key(old)) {
            None => {
                self.insert_right(new);
                None
            },
            Some(mut r) => {
                let set: HashSet<(u64, u64)> = r.pairs.drain().collect();
                let new_hash = make_hash::<R, S>(&self.hash_builder, &new);
                let item = RightItem { value: new, pairs: set.clone(), id: self.counter };
                self.right_set.insert(new_hash, item, make_hasher(&self.hash_builder));
                self.counter += 1;
                for (hash, id) in set {
                    self.left_set.get_mut(hash, left_just_id(id)).unwrap().hash = new_hash;
                }
                Some(r.value)
            }
        }
    }

    /// Pairs two existing items in the map. Returns `true` if they were successfully paired.
    /// Returns `false` if either item can not be found or if either items is already paired.
    ///
    /// Use [`pair_forced`] if you want to break the existing pairings.
    ///
    /// [`pair_forced`]: struct.GroupMap.html#method.pair_forced
    pub fn pair(&mut self, left: &L, right: &R) -> bool {
        let l_hash = make_hash::<L, S>(&self.hash_builder, left);
        let r_hash = make_hash::<R, S>(&self.hash_builder, right);
        let opt_left = self.left_set.get_mut(l_hash, equivalent_key(left));
        let opt_right = self.right_set.get_mut(r_hash, equivalent_key(right));
        let (digest, to_remove) = match (opt_left, opt_right) {
            (Some(left), Some(_)) => {
                let to_remove = Some((left.hash, left.id));
                left.hash = r_hash;
                (true, to_remove)
            }
            _ => (false, None),
        };
        // The specified right item is updated here to avoid potential collision should hash ==
        // r_hash
        if let Some((hash, id)) = to_remove {
            let old_right = self
                .right_set
                .get_mut(hash, right_hash_and_id(&(l_hash, id)))
                .unwrap();
            old_right.pairs.remove(&(l_hash, id));
            let new_right = self
                .right_set
                .get_mut(r_hash, equivalent_key(right))
                .unwrap();
            new_right.pairs.insert((l_hash, id));
        }
        digest
    }

    /// Determines if an item in the right set is paired.
    ///
    /// Returns false if the item isn't found or is unpaired. Returns true otherwise.
    pub fn is_right_paired(&self, right: &R) -> bool {
        let r_hash = make_hash::<R, S>(&self.hash_builder, right);
        let opt_right = self.right_set.get(r_hash, equivalent_key(right));
        match opt_right {
            Some(r) => r.pairs.is_empty(),
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
        let opt_left = self.left_set.get(l_hash, equivalent_key(left));
        let opt_right = self.right_set.get(r_hash, equivalent_key(right));
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
        self.left_set.get(hash, equivalent_key(left)).is_some()
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
        self.right_set.get(hash, equivalent_key(right)).is_some()
    }

    /// Removes a pair of items only if they are paired together and returns the pair
    pub fn remove(&mut self, left: &L, right: &R) -> Option<(Vec<L>, R)> {
        if self.are_paired(left, right) {
            self.remove_right(right)
        } else {
            None
        }
    }

    /// Removes the given item from the left set and its associated item from the right set
    pub fn remove_left(&mut self, item: &L) -> Option<L> {
        let l_hash = make_hash::<L, S>(&self.hash_builder, item);
        let left_item = self.left_set.remove_entry(l_hash, equivalent_key(item))?;
        let pair = (l_hash, left_item.id);
        self.right_set
            .get_mut(left_item.hash, right_hash_and_id(&pair))
            .unwrap()
            .pairs
            .remove(&pair);
        Some(left_item.extract())
    }

    /// Removes the given item from the right set and its associated item from the left set
    pub fn remove_right(&mut self, item: &R) -> Option<(Vec<L>, R)> {
        let r_hash = make_hash::<R, S>(&self.hash_builder, item);
        let right_item = self.right_set.remove_entry(r_hash, equivalent_key(item))?;
        let left_vec: Vec<L> = right_item
            .pairs
            .iter()
            .map(|(h, i)| {
                self.left_set
                    .remove_entry(*h, left_hash_and_id(r_hash, *i))
                    .unwrap()
                    .extract()
            })
            .collect();
        Some((left_vec, right_item.extract()))
    }

    /// Removes a pair using the hash of the left item, right item, and their shared pairing id
    fn remove_via_hash_and_id(&mut self, r_hash: u64, id: u64) -> Option<(Vec<L>, R)> {
        let right = self.right_set.remove_entry(r_hash, right_just_id(id))?;
        let left_vec = right
            .pairs
            .iter()
            .map(|(h, i)| {
                self.left_set
                    .remove_entry(*h, left_hash_and_id(r_hash, *i))
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
    pub fn get_left_iter(&self, item: &R) -> Option<PairIter<'_, L, R, S>> {
        let r_hash = make_hash::<R, S>(&self.hash_builder, item);
        let right_item: &RightItem<R> = self.right_set.get(r_hash, equivalent_key(item))?;
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
    pub fn get_right(&self, item: &L) -> Option<&R> {
        let l_hash = make_hash::<L, S>(&self.hash_builder, item);
        let left_item: &LeftItem<L> = self.get_left_inner_with_hash(item, l_hash)?;
        match self
            .right_set
            .get(left_item.hash, right_hash_and_id(&(l_hash, left_item.id)))
        {
            None => None,
            Some(pairing) => Some(&pairing.value),
        }
    }


    #[inline]
    fn get_left_inner_with_hash(&self, item: &L, hash: u64) -> Option<&LeftItem<L>> {
        self.left_set.get(hash, equivalent_key(item))
    }

    #[inline]
    fn get_right_inner_with_hash(&self, item: &R, hash: u64) -> Option<&RightItem<R>> {
        self.right_set.get(hash, equivalent_key(item))
    }

    /// Returns an iterator over the items in the map
    pub fn iter(&self) -> Iter<'_, L, R, S> {
        Iter {
            right_iter: unsafe { self.right_set.iter() },
            left_iter: None,
            map_ref: self,
        }
    }

    /// Returns an iterator over the paired items in the map
    pub fn iter_paired(&self) -> PairedIter<'_, L, R, S> {
        PairedIter {
            left_iter: unsafe { self.left_set.iter() },
            map_ref: self,
        }
    }

    /// Returns an iterator over the unpaired items in the map
    pub fn iter_unpaired(&self) -> UnpairedIter<'_, L, R, S> {
        UnpairedIter {
            right_iter: unsafe { self.right_set.iter() },
            map_ref: self,
        }
    }

    /// Returns an iterator over elements in the left set
    pub fn iter_left(&self) -> LeftIter<'_, L> {
        LeftIter {
            left_iter: unsafe { self.left_set.iter() },
            marker: PhantomData,
        }
    }

    /// Returns an iterator over elements in the right set
    pub fn iter_right(&self) -> RightIter<'_, R> {
        RightIter {
            right_iter: unsafe { self.right_set.iter() },
            marker: PhantomData,
        }
    }

    /// Drops all items that cause the predicate to return `false` while keeping the backing memory
    /// allocated
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(Option<&L>, &R) -> bool,
    {
        // right hash, left id
        let mut to_drop: Vec<(u64, u64)> = Vec::with_capacity(self.left_set.len());
        for (opt_l, r) in self.iter() {
            if f(opt_l, r) {
                let r_hash = make_hash::<R, S>(&self.hash_builder, r);
                let r_item = self.get_right_inner_with_hash(r, r_hash).unwrap();
                to_drop.push((r_hash, r_item.id));
            }
        }
        for (r_hash, id) in to_drop {
            self.remove_via_hash_and_id(r_hash, id);
        }
    }

    /// Drops all pairs that cause the predicate to return `false` while keeping the backing memory
    /// allocated
    pub fn retain_paired<F>(&mut self, mut f: F)
    where
        F: FnMut(&L, &R) -> bool,
    {
        // right hash, left id
        let mut to_drop: Vec<(u64, u64)> = Vec::with_capacity(self.left_set.len());
        for (l, r) in self.iter_paired() {
            if f(l, r) {
                let r_hash = make_hash::<R, S>(&self.hash_builder, r);
                let r_item = self.get_right_inner_with_hash(r, r_hash).unwrap();
                to_drop.push((r_hash, r_item.id));
            }
        }
        for (r_hash, id) in to_drop {
            self.remove_via_hash_and_id(r_hash, id);
        }
    }

    /// Drops all unpaired items that cause the predicate to return `false` while keeping the backing memory
    /// allocated
    pub fn retain_unpaired<F>(&mut self, mut f: F)
    where
        F: FnMut(&R) -> bool,
    {
        // right hash, left id
        let mut to_drop: Vec<(u64, u64)> = Vec::with_capacity(self.left_set.len());
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
            counter: self.counter,
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
    /// Creates a GroupMap that uses the given hasher
    pub const fn with_hasher(hash_builder: S) -> Self {
        Self {
            hash_builder,
            counter: 0,
            left_set: RawTable::new(),
            right_set: RawTable::new(),
        }
    }

    /// Creates a GroupMap that uses the given hasher and whose inner sets each have the given capacity
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

    /// Returns the len of the inner sets (same between sets)
    pub fn len_left(&self) -> usize {
        // The size of the sets is always equal
        self.left_set.len()
    }

    /// Returns the len of the inner sets (same between sets)
    pub fn len_right(&self) -> usize {
        // The size of the sets is always equal
        self.right_set.len()
    }

    /// Returns true if no items are in the map and false otherwise
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
                if self.contains_right(&right) {
                    self.insert_left(l, &right);
                } else {
                    self.insert(l, right);
                }
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
            if self.contains_right(&right) {
                self.insert_left(left, &right);
            } else {
                self.insert(left, right);
            }
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
    left_iter: Option<hash_set::Iter<'a, (u64, u64)>>,
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
                    .get(pair.0, left_just_id(pair.1))
                    .unwrap();
                let right = self
                    .map_ref
                    .right_set
                    .get(left.hash, right_hash_and_id(pair))
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
                        .get(pair.0, left_just_id(pair.1))
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
            Some(l_bucket) => unsafe {
                let l_item = l_bucket.as_ref();
                let l_hash = make_hash::<L, S>(self.map_ref.hasher(), &l_item.value);
                let r_item = self
                    .map_ref
                    .right_set
                    .get(l_item.hash, right_hash_and_id(&(l_hash, l_item.id)))
                    .unwrap();
                return Some((&l_item.value, &r_item.value));
            },
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
    iter: hash_set::Iter<'a, (u64, u64)>,
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
                .get(*hash, left_just_id(*id))
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

impl<T: PartialEq> PartialEq<T> for LeftItem<T> {
    fn eq(&self, other: &T) -> bool {
        self.value.eq(other)
    }
}

impl<T: Eq> Eq for LeftItem<T> {}

impl<T: Clone> Clone for LeftItem<T> {
    fn clone(&self) -> Self {
        Self {
            value: self.value.clone(),
            hash: self.hash,
            id: self.id,
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for LeftItem<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "LeftItem {{ value: {:?}, hash: {}, id: {} }}",
            self.value, self.hash, self.id
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

impl<T: PartialEq> PartialEq<T> for RightItem<T> {
    fn eq(&self, other: &T) -> bool {
        self.value.eq(other)
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
            self.value, self.id, self.pairs
        )
    }
}
