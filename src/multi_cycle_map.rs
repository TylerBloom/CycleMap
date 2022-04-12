use std::{
    default::Default,
    fmt,
    hash::{BuildHasher, Hash},
    iter::{FusedIterator, Map},
};

use hashbrown::{
    hash_map::DefaultHashBuilder,
    hash_set,
    raw::{Bucket, RawIter, RawTable},
    HashSet,
};

use crate::optionals::*;
use crate::utils::*;
use OptionalPair::*;

pub(crate) fn equivalent_key<T: PartialEq<Q>, Q: PartialEq + ?Sized>(
    k: &Q,
) -> impl Fn(&T) -> bool + '_ {
    move |x| x.eq(k)
}

pub(crate) fn left_hash_and_id<'a, T: PartialEq + ?Sized>(
    hash: u64,
    id: u64,
) -> impl Fn(&LeftItem<T>) -> bool + 'a {
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

/// Similar to [`CycleMap`] but items might be not paired.
///
/// [`CycleMap`]: crate.struct.CycleMap.html
pub struct MultiCycleMap<L, R, St = DefaultHashBuilder> {
    pub(crate) hash_builder: St,
    pub(crate) counter: u64,
    left_set: RawTable<LeftItem<L>>,
    right_set: RawTable<RightItem<R>>,
}

impl<L, R> MultiCycleMap<L, R, DefaultHashBuilder> {
    #[inline]
    /// Creates a new MultiCycleMap
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    /// Creates a new MultiCycleMap whose inner sets each of the given capacity
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, DefaultHashBuilder::default())
    }
}

impl<L, R, S> MultiCycleMap<L, R, S>
where
    L: Eq + Hash,
    R: Eq + Hash,
    S: BuildHasher,
{
    /// Adds a pair of items to the map.
    ///
    /// Should the left element be equal to another left element, the old pair is removed and
    /// returned. The same goes for the right element.
    ///
    /// There is a chance for collision here. Collision occurs when the map contains elements with
    /// identical hashes as the given left and right elements, and they are mapped to each other.
    /// In such a case, the old pair is returned and the new pair is inserted.
    pub fn insert(&mut self, left: L, right: R) -> (Option<L>, Option<(Vec<L>, R)>) {
        let opt_from_left = self.remove_via_left(&left);
        let opt_from_right = self.remove_via_right(&right);
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
    /// [`swap_left`]: struct.MultiCycleMap.html#method.swap_left
    pub fn insert_left(&mut self, left: L, right: &R) -> Option<L> {
        let r_hash = make_hash::<R, S>(&self.hash_builder, &right);
        let right_item = self.right_set.get_mut(r_hash, equivalent_key(right))?;
        let digest = self.remove_via_left(&left);
        let l_hash = make_hash::<L, S>(&self.hash_builder, &left);
        right_item.pairs.insert((l_hash, self.counter));
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
    /// [`swap_right`]: struct.MultiCycleMap.html#method.swap_right
    pub fn insert_right(&mut self, right: R) -> Option<(Vec<L>, R)> {
        let opt_from_right = self.remove_via_right(&right);
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

    /// Pairs two existing items in the map. Returns `true` if they were successfully paired.
    /// Returns `false` if either item can not be found or if either items is already paired.
    ///
    /// Use [`pair_forced`] if you want to break the existing pairings.
    ///
    /// [`pair_forced`]: struct.MultiCycleMap.html#method.pair_forced
    pub fn pair(&mut self, left: &L, right: &R) -> bool {
        let l_hash = make_hash::<L, S>(&self.hash_builder, left);
        let r_hash = make_hash::<R, S>(&self.hash_builder, right);
        let opt_left = self.left_set.get_mut(l_hash, equivalent_key(left));
        let opt_right = self.right_set.get_mut(r_hash, equivalent_key(right));
        match (opt_left, opt_right) {
            (Some(left), Some(right)) => {
                right.pairs.insert((l_hash, left.id));
                left.hash = r_hash;
                true
            }
            _ => false,
        }
    }

    /// Determines if an item in the right set is paired.
    ///
    /// Returns false if the item isn't found or is unpaired. Returns true otherwise.
    pub fn is_right_paired(&self, right: &R) -> bool {
        let r_hash = make_hash::<R, S>(&self.hash_builder, right);
        let opt_right = self.right_set.get(r_hash, equivalent_key(right));
        match opt_right {
            Some(r) => r.pairs.len() != 0,
            None => false,
        }
    }

    /// Determines if two items are mapped to one another
    ///
    /// Returns false if either item isn't found it its associated list.
    pub fn are_mapped(&self, left: &L, right: &R) -> bool {
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

    /// Determines if the mapped contains the item in the left set
    ///
    /// Returns `true` if the item is found and `false` otherwise.
    pub fn contains_left(&self, left: &L) -> bool {
        let hash = make_hash::<L, S>(&self.hash_builder, left);
        self.left_set.get(hash, equivalent_key(left)).is_some()
    }

    /// Determines if the mapped contains the item in the right set
    ///
    /// Returns `true` if the item is found and `false` otherwise.
    pub fn contains_right(&self, right: &R) -> bool {
        let hash = make_hash::<R, S>(&self.hash_builder, right);
        self.right_set.get(hash, equivalent_key(right)).is_some()
    }

    /// Removes a pair of items only if they are mapped together and returns the pair
    pub fn remove(&mut self, left: &L, right: &R) -> Option<(Vec<L>, R)> {
        if self.are_mapped(left, right) {
            self.remove_via_right(right)
        } else {
            None
        }
    }

    /// Removes the given item from the left set and its associated item from the right set
    pub fn remove_via_left(&mut self, item: &L) -> Option<L> {
        let l_hash = make_hash::<L, S>(&self.hash_builder, item);
        let left_item: LeftItem<L> =
            if let Some(p) = self.left_set.remove_entry(l_hash, equivalent_key(item)) {
                p
            } else {
                return None;
            };
        let pair = (l_hash, left_item.id);
        self.right_set
            .get_mut(left_item.hash, right_hash_and_id(&pair))
            .unwrap()
            .pairs
            .remove(&pair);
        Some(left_item.extract())
    }

    /// Removes the given item from the right set and its associated item from the left set
    pub fn remove_via_right(&mut self, item: &R) -> Option<(Vec<L>, R)> {
        let r_hash = make_hash::<R, S>(&self.hash_builder, item);
        let right_item: RightItem<R> =
            if let Some(p) = self.right_set.remove_entry(r_hash, equivalent_key(item)) {
                p
            } else {
                return None;
            };
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
        None
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

    /// Returns an optional iterator over the items that the given item is paired with.
    /// `None` is returned if the given item can't be found.
    pub fn get_left_iter(&self, item: &R) -> Option<&L> {
        todo!()
    }

    /// Gets a reference to an item in the right set using an item in the left set.
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

    /* Might need again... unlikely though
    /// Removes a pair using the hash of the left item, right item, and their shared pairing id
    fn get_via_hashes_and_id(&self, l_hash: u64, r_hash: u64, id: u64) -> Option<(&L, &R)> {
    let left_item = self.left_set.get(l_hash, hash_and_id(r_hash, id))?;
    let right_item = self.right_set.get(r_hash, hash_and_id(l_hash, id)).unwrap();
    Some((&left_item.value, &right_item.value))
    }
    */

    #[inline]
    fn get_left_inner(&self, item: &L) -> Option<&LeftItem<L>> {
        let hash = make_hash::<L, S>(&self.hash_builder, item);
        self.left_set.get(hash, equivalent_key(item))
    }

    #[inline]
    fn get_left_inner_with_hash(&self, item: &L, hash: u64) -> Option<&LeftItem<L>> {
        self.left_set.get(hash, equivalent_key(item))
    }

    #[inline]
    fn get_right_inner(&self, item: &R) -> Option<&RightItem<R>> {
        let hash = make_hash::<R, S>(&self.hash_builder, item);
        self.right_set.get(hash, equivalent_key(item))
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
    pub fn iter_mapped(&self) -> MappedIter<'_, L, R, S> {
        MappedIter {
            left_iter: unsafe { self.left_set.iter() },
            map_ref: self,
        }
    }

    /// Returns an iterator over the unpaired items in the map
    pub fn iter_unmapped(&self) -> UnmappedIter<'_, L, R, S> {
        //let closure: P = move |b| { b.as_ref().pairs.len() == 0 };
        UnmappedIter {
            right_iter: unsafe { self.right_set.iter() },
            map_ref: self,
        }
    }

    /// Returns an iterator over elements in the left set
    pub fn iter_left(&self) -> LeftIter<L> {
        LeftIter {
            iter: unsafe { self.left_set.iter() },
        }
    }

    /// Returns an iterator over elements in the right set
    pub fn iter_right(&self) -> RightIter<R> {
        RightIter {
            iter: unsafe { self.right_set.iter() },
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
            if !f(opt_l, r) {
                let r_hash = make_hash::<R, S>(&self.hash_builder, &r);
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
    pub fn retain_mapped<F>(&mut self, mut f: F)
    where
        F: FnMut(&L, &R) -> bool,
    {
        // right hash, left id
        let mut to_drop: Vec<(u64, u64)> = Vec::with_capacity(self.left_set.len());
        for (l, r) in self.iter_mapped() {
            if !f(l, r) {
                let r_hash = make_hash::<R, S>(&self.hash_builder, &r);
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
    pub fn retain_unmapped<F>(&mut self, mut f: F)
    where
        F: FnMut(&R) -> bool,
    {
        // right hash, left id
        let mut to_drop: Vec<(u64, u64)> = Vec::with_capacity(self.left_set.len());
        for r in self.iter_unmapped() {
            if !f(r) {
                let r_hash = make_hash::<R, S>(&self.hash_builder, &r);
                let r_item = self.get_right_inner_with_hash(r, r_hash).unwrap();
                to_drop.push((r_hash, r_item.id));
            }
        }
        for (r_hash, id) in to_drop {
            self.remove_via_hash_and_id(r_hash, id);
        }
    }
}

impl<L, R, S> Clone for MultiCycleMap<L, R, S>
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

impl<L, R, S> Default for MultiCycleMap<L, R, S>
where
    S: Default,
{
    fn default() -> Self {
        Self::with_hasher(Default::default())
    }
}

impl<L, R, S> fmt::Debug for MultiCycleMap<L, R, S>
where
    L: Hash + Eq + fmt::Debug,
    R: Hash + Eq + fmt::Debug,
    S: BuildHasher,
{
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_set().entries(self.iter()).finish()
    }
}

impl<L, R, S> PartialEq<MultiCycleMap<L, R, S>> for MultiCycleMap<L, R, S>
where
    L: Hash + Eq + fmt::Debug,
    R: Hash + Eq + fmt::Debug,
    S: BuildHasher,
{
    fn eq(&self, other: &Self) -> bool {
        if self.len_left() != other.len_left() && self.len_right() != other.len_right() {
            return false;
        }
        self.iter().all(|op| match op {
            SomeLeft(l) => other.get_right(l).is_none(),
            SomeRight(r) => other.get_left(r).is_none(),
            SomeBoth(l, r) => other.are_mapped(l, r),
            _ => {
                unreachable!("There has to be at least one item.")
            }
        })
    }
}

impl<L, R, S> Eq for MultiCycleMap<L, R, S>
where
    L: Hash + Eq + fmt::Debug,
    R: Hash + Eq + fmt::Debug,
    S: BuildHasher,
{
}

impl<L, R, S> MultiCycleMap<L, R, S> {
    /// Creates a MultiCycleMap that uses the given hasher
    pub const fn with_hasher(hash_builder: S) -> Self {
        Self {
            hash_builder,
            counter: 0,
            left_set: RawTable::new(),
            right_set: RawTable::new(),
        }
    }

    /// Creates a MultiCycleMap that uses the given hasher and whose inner sets each have the given capacity
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        Self {
            hash_builder,
            counter: 0,
            left_set: RawTable::with_capacity(capacity),
            right_set: RawTable::with_capacity(capacity),
        }
    }

    /// Returns a reference to the hasher used by the map
    pub fn hasher(&self) -> &S {
        &self.hash_builder
    }

    /// Returns the capacity of the left set
    pub fn capacity_left(&self) -> usize {
        // The size of the sets is always equal
        self.left_set.capacity()
    }

    /// Returns the capacity of the right set
    pub fn capacity_right(&self) -> usize {
        // The size of the sets is always equal
        self.right_set.capacity()
    }

    /* Might be used in the future
    /// Returns the raw capacity of the inner sets (same between sets)
    fn raw_capacity(&self) -> usize {
    // The size of the sets is always equal
    self.left_set.buckets()
    }
    */

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

    /// Removes all pairs for the set while keeping the backing memory allocated
    pub fn clear(&mut self) {
        self.left_set.clear();
        self.right_set.clear();
    }
}

impl<L, R, S> Extend<(L, R)> for MultiCycleMap<L, R, S>
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

impl<L, R> FromIterator<(L, R)> for MultiCycleMap<L, R>
where
    L: Hash + Eq,
    R: Hash + Eq,
{
    fn from_iter<T: IntoIterator<Item = (L, R)>>(iter: T) -> Self {
        let mut digest = MultiCycleMap::default();
        digest.extend(iter);
        digest
    }
}

/// An iterator over the entry items of a `MultiCycleMap`.
pub struct Iter<'a, L, R, S> {
    right_iter: RawIter<RightItem<R>>,
    left_iter: Option<hash_set::Iter<'a, (u64, u64)>>,
    map_ref: &'a MultiCycleMap<L, R, S>,
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
                if r_ref.pairs.len() == 0 {
                    return Some((None, &r_ref.value));
                } else {
                    let iter = r_ref.pairs.iter();
                    let pair = iter.next().unwrap();
                    self.left_iter = Some(iter);
                    let left = self
                        .map_ref
                        .left_set
                        .get(pair.0, left_just_id(pair.1))
                        .unwrap();
                    return Some((Some(&left.value), &r_ref.value));
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

/// An iterator over the entry pairs of a `MultiCycleMap`.
pub struct MappedIter<'a, L, R, S> {
    left_iter: RawIter<LeftItem<L>>,
    map_ref: &'a MultiCycleMap<L, R, S>,
}

impl<L, R, S> Clone for MappedIter<'_, L, R, S> {
    fn clone(&self) -> Self {
        Self {
            left_iter: self.left_iter.clone(),
            map_ref: self.map_ref,
        }
    }
}

impl<L, R, S> fmt::Debug for MappedIter<'_, L, R, S>
where
    L: Hash + Eq + fmt::Debug,
    R: Hash + Eq + fmt::Debug,
    S: BuildHasher,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, L, R, S> Iterator for MappedIter<'a, L, R, S>
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

impl<'a, L, R, S> ExactSizeIterator for MappedIter<'a, L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
    fn len(&self) -> usize {
        self.clone().count()
    }
}

impl<L, R, S> FusedIterator for MappedIter<'_, L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
}

/// An iterator over the entry pairs of a `MultiCycleMap`.
pub struct UnmappedIter<'a, L, R, S> {
    right_iter: RawIter<RightItem<R>>,
    map_ref: &'a MultiCycleMap<L, R, S>,
}

impl<L, R, S> Clone for UnmappedIter<'_, L, R, S> {
    fn clone(&self) -> Self {
        Self {
            right_iter: self.right_iter.clone(),
            map_ref: self.map_ref,
        }
    }
}

impl<L, R, S> fmt::Debug for UnmappedIter<'_, L, R, S>
where
    L: Hash + Eq + fmt::Debug,
    R: Hash + Eq + fmt::Debug,
    S: BuildHasher,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, L, R, S> Iterator for UnmappedIter<'a, L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
    type Item = &'a R;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(item) = self.right_iter.next().map(|r| unsafe { &r.as_ref() }) {
            if item.pairs.len() == 0 {
                return Some(&item.value);
            }
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.right_iter.size_hint()
    }
}

impl<'a, L, R, S> ExactSizeIterator for UnmappedIter<'a, L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
    fn len(&self) -> usize {
        self.clone().count()
    }
}

impl<L, R, S> FusedIterator for UnmappedIter<'_, L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
}

/// An iterator over the elements of an inner set of a `MultiCycleMap`.
pub struct LeftIter<I> {
    iter: I,
}

impl<I> Clone for LeftIter<I>
where
    I: Clone,
{
    fn clone(&self) -> Self {
        Self {
            iter: self.iter.clone(),
        }
    }
}

impl<I> fmt::Debug for LeftIter<I>
where
    I: Iterator + Clone,
    <I as Iterator>::Item: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, I> Iterator for LeftIter<I>
where
    I: Iterator,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, I> ExactSizeIterator for LeftIter<I>
where
    I: ExactSizeIterator,
{
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<I> FusedIterator for LeftIter<I> where I: FusedIterator {}

/// An iterator over the elements of an inner set of a `MultiCycleMap`.
pub struct RightIter<'_, R> {
    right_iter: RawIter<RightItem<R>>,
}

impl<R> Clone for RightIter<R> {
    fn clone(&self) -> Self {
        Self {
            right_iter: self.right_iter.clone(),
        }
    }
}

impl<R> fmt::Debug for RightIter<'_, R>
where
    Self: Clone,
    R: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, R> Iterator for RightIter<'a, R>
{
    type Item = &'a R;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(right) = self.iter.next() {
            unsafe { Some(&right.as_ref().value) }
        }
        None
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<'a, I> ExactSizeIterator for RightIter<I>
where
    I: ExactSizeIterator,
{
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<I> FusedIterator for RightIter<I> where I: FusedIterator {}

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

#[cfg(test)]
mod tests {
    use std::hash::Hash;

    use super::MultiCycleMap;

    #[derive(PartialEq, Eq, Hash, Debug)]
    struct TestingStruct {
        pub(crate) value: u64,
        pub(crate) data: String,
    }

    fn construct_default_map() -> MultiCycleMap<String, TestingStruct> {
        (0..100)
            .map(|i| (i.to_string(), TestingStruct::new(i, i.to_string())))
            .collect()
    }

    #[test]
    fn default_construction_test() {
        let map = construct_default_map();
        assert_eq!(map.len_left(), 100);
        assert_eq!(map.len_right(), 100);
    }

    /* Might be needed in the future
    #[test]
    fn get_inner_tests() {
    let map = construct_default_map();
    for i in 0..100 {
    let i_str = i.to_string();
    let i_struct = TestingStruct::new(i, i.to_string());
    let l_hash = make_hash::<String, DefaultHashBuilder>(map.hasher(), &i_str);
    let r_hash = make_hash::<TestingStruct, DefaultHashBuilder>(map.hasher(), &i_struct);
    let left_opt = map.get_left_inner(&i_str);
    assert!(left_opt.is_some());
    let l_item = left_opt.unwrap();
    assert_eq!(l_item.value, i_str);
    assert_eq!(l_item.hash, r_hash);
    let right_opt = map.get_right_inner(&i_struct);
    assert!(right_opt.is_some());
    let r_item = right_opt.unwrap();
    assert_eq!(r_item.value, i_struct);
    assert_eq!(r_item.hash, l_hash);
    }
    }
    */

    /* Should the take methods be needed for the drain iters, these tests will make a return
    #[test]
    fn take_left_tests() {
    let mut map = construct_default_map();
    for i in 0..100 {
    let i_str = i.to_string();
    let i_struct = TestingStruct::new(i, i.to_string());
    let r_hash = make_hash::<TestingStruct, DefaultHashBuilder>(map.hasher(), &i_struct);
    let take_opt = unsafe { map.take_left(&i_struct) };
    assert!(take_opt.is_some());
    let pairing = take_opt.unwrap();
    assert_eq!(pairing.value, i_str);
    assert_eq!(pairing.hash, r_hash);
    }
    }

    #[test]
    fn take_right_tests() {
    let mut map = construct_default_map();
    for i in 0..100 {
    let i_str = i.to_string();
    let i_struct = TestingStruct::new(i, i.to_string());
    let l_hash = make_hash::<String, DefaultHashBuilder>(map.hasher(), &i_str);
    let take_opt = unsafe { map.take_right(&i_str) };
    assert!(take_opt.is_some());
    let pairing = take_opt.unwrap();
    assert_eq!(pairing.value, i_struct);
    assert_eq!(pairing.hash, l_hash);
    }
    }
    */

    impl TestingStruct {
        pub(crate) fn new(value: u64, data: String) -> Self {
            Self { value, data }
        }
    }
}
