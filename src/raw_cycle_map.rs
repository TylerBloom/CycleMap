use std::{
    default::Default,
    fmt,
    hash::{BuildHasher, Hash},
    iter::FusedIterator,
    marker::PhantomData,
};

use core::mem;

use hashbrown::{
    hash_map::DefaultHashBuilder,
    raw::{Bucket, RawDrain, RawIter, RawTable},
    TryReserveError,
};

use crate::{optionals::*, utils::*};
use OptionalPair::*;

#[cfg(doc)]
use crate::CycleMap;

// Contains a value and the hash of the item that the value maps to.
pub struct MappingPair<T> {
    pub value: T,
    pub hash: Option<u64>,
    pub id: u64,
}

pub fn equivalent_key<Q: PartialEq + ?Sized>(k: &Q) -> impl Fn(&MappingPair<Q>) -> bool + '_ {
    move |x| k.eq(&x.value)
}

pub fn hash_and_id<'a, Q: PartialEq + ?Sized>(
    hash: u64,
    id: u64,
) -> impl Fn(&MappingPair<Q>) -> bool + 'a {
    move |x| id == x.id && Some(hash) == x.hash
}

// To be safe, use `hash_and_id` whenever possible
pub fn just_id<'a, Q: PartialEq + ?Sized>(id: u64) -> impl Fn(&MappingPair<Q>) -> bool + 'a {
    move |x| id == x.id
}

/// `RawCycleMap` enforces the core invariant of enabling bi-directional lookups. It does not
/// enforce any other invariants. It is meant to be the inner type for a wrapper map types that
/// enforce additional invariants.
pub struct RawCycleMap<L, R, St = DefaultHashBuilder> {
    pub hash_builder: St,
    pub counter: u64,
    pub left_set: RawTable<MappingPair<L>>,
    pub right_set: RawTable<MappingPair<R>>,
}

impl<L, R> RawCycleMap<L, R, DefaultHashBuilder> {
    #[inline]
    /// Creates a new `RawCycleMap`.
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    /// Creates a new, empty `RawCycleMap` with inner sets that each have at least the given capacity
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, DefaultHashBuilder::default())
    }
}

impl<L, R, S> RawCycleMap<L, R, S>
where
    L: Eq + Hash,
    R: Eq + Hash,
    S: BuildHasher,
{
    /// Adds a pair of items to the map.
    ///
    /// Note: There is no check for items that are equal.
    pub fn insert(&mut self, left: L, right: R) {
        let l_hash = make_hash::<L, S>(&self.hash_builder, &left);
        let r_hash = make_hash::<R, S>(&self.hash_builder, &right);
        let left_pairing = MappingPair {
            value: left,
            hash: Some(r_hash),
            id: self.counter,
        };
        let right_pairing = MappingPair {
            value: right,
            hash: Some(l_hash),
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
    }

    /// Adds an item to the left set of the map.
    ///
    /// Note: There is no check for items that are equal.
    pub fn insert_left(&mut self, left: L) {
        let l_hash = make_hash::<L, S>(&self.hash_builder, &left);
        let left_pairing = MappingPair {
            value: left,
            hash: None,
            id: self.counter,
        };
        self.counter += 1;
        self.left_set.insert(
            l_hash,
            left_pairing,
            make_hasher::<MappingPair<L>, S>(&self.hash_builder),
        );
    }

    /// Adds an item to the right set of the map.
    ///
    /// Note: There is no check for items that are equal.
    pub fn insert_right(&mut self, right: R) {
        let r_hash = make_hash::<R, S>(&self.hash_builder, &right);
        let right_pairing = MappingPair {
            value: right,
            hash: None,
            id: self.counter,
        };
        self.counter += 1;
        self.right_set.insert(
            r_hash,
            right_pairing,
            make_hasher::<MappingPair<R>, S>(&self.hash_builder),
        );
    }

    /// Pairs two existing items in the map. Returns `true` if they were successfully paired.
    /// Returns `false` if either item can not be found or if either items is already paired.
    pub fn pair(&mut self, left: &L, right: &R) -> bool {
        let l_hash = make_hash::<L, S>(&self.hash_builder, left);
        let r_hash = make_hash::<R, S>(&self.hash_builder, right);
        let opt_left = self.left_set.get_mut(l_hash, equivalent_key(left));
        let opt_right = self.right_set.get_mut(r_hash, equivalent_key(right));
        match (opt_left, opt_right) {
            (Some(left), Some(right)) => match (left.hash, right.hash) {
                (None, None) => {
                    left.hash = Some(r_hash);
                    right.hash = Some(l_hash);
                    right.id = left.id;
                    true
                }
                _ => false,
            },
            _ => false,
        }
    }

    /// Pairs two existing items in the map. Items that are paired become unpaired but remain in
    /// the map. References to items that become unpaired are returned.
    pub fn pair_forced(&mut self, l: &L, r: &R) -> OptionalPair<&L, &R> {
        if self.are_paired(l, r) {
            return Neither;
        }
        let l_hash = make_hash::<L, S>(&self.hash_builder, l);
        let r_hash = make_hash::<R, S>(&self.hash_builder, r);
        let opt_left = self.left_set.get_mut(l_hash, equivalent_key(l));
        let opt_right = self.right_set.get_mut(r_hash, equivalent_key(r));
        match (opt_left, opt_right) {
            (Some(left), Some(right)) => match (left.hash, right.hash) {
                (None, None) => {
                    left.hash = Some(r_hash);
                    right.hash = Some(l_hash);
                    right.id = left.id;
                    Neither
                }
                (Some(lp_hash), None) => {
                    left.hash = Some(r_hash);
                    right.hash = Some(l_hash);
                    let old_id = left.id;
                    // Here, we give the left item the new id to avoid a collision in the right set
                    left.id = right.id;
                    self.right_set
                        .get_mut(lp_hash, hash_and_id(l_hash, old_id))
                        .unwrap()
                        .hash = None;
                    SomeRight(&self.right_set.get(lp_hash, just_id(old_id)).unwrap().value)
                }
                (None, Some(rp_hash)) => {
                    left.hash = Some(r_hash);
                    right.hash = Some(l_hash);
                    let old_id = right.id;
                    // Here, we give the right item the new id to avoid a collision in the left set
                    right.id = left.id;
                    self.left_set
                        .get_mut(rp_hash, hash_and_id(r_hash, old_id))
                        .unwrap()
                        .hash = None;
                    SomeLeft(&self.left_set.get(rp_hash, just_id(old_id)).unwrap().value)
                }
                (Some(lp_hash), Some(rp_hash)) => {
                    left.hash = Some(r_hash);
                    right.hash = Some(l_hash);
                    let old_l_id = left.id;
                    let old_r_id = right.id;
                    // Here, we give the pair a new id to avoid collisions in both sets
                    left.id = self.counter;
                    right.id = self.counter;
                    self.counter += 1;
                    self.left_set
                        .get_mut(rp_hash, hash_and_id(r_hash, old_r_id))
                        .unwrap()
                        .hash = None;
                    self.right_set
                        .get_mut(lp_hash, hash_and_id(l_hash, old_l_id))
                        .unwrap()
                        .hash = None;
                    SomeBoth(
                        &self.left_set.get(rp_hash, just_id(old_r_id)).unwrap().value,
                        &self
                            .right_set
                            .get(lp_hash, just_id(old_l_id))
                            .unwrap()
                            .value,
                    )
                }
            },
            _ => Neither,
        }
    }

    /// Pairs two existing items in the map. Items that are paired become unpaired and are removed
    /// from the map. The old items are returned.
    pub fn pair_remove(&mut self, l: &L, r: &R) -> OptionalPair<L, R> {
        if self.are_paired(l, r) {
            return Neither;
        }
        let l_hash = make_hash::<L, S>(&self.hash_builder, l);
        let r_hash = make_hash::<R, S>(&self.hash_builder, r);
        let opt_left = self.left_set.get_mut(l_hash, equivalent_key(l));
        let opt_right = self.right_set.get_mut(r_hash, equivalent_key(r));
        match (opt_left, opt_right) {
            (Some(left), Some(right)) => {
                match (left.hash, right.hash) {
                    (None, None) => {
                        left.hash = Some(r_hash);
                        right.hash = Some(l_hash);
                        right.id = left.id;
                        Neither
                    }
                    (Some(lp_hash), None) => {
                        left.hash = Some(r_hash);
                        right.hash = Some(l_hash);
                        let old_id = left.id;
                        // Here, we give the left item the new id to avoid a collision in the right set
                        left.id = right.id;
                        SomeRight(
                            self.right_set
                                .remove_entry(lp_hash, just_id(old_id))
                                .unwrap()
                                .extract(),
                        )
                    }
                    (None, Some(rp_hash)) => {
                        left.hash = Some(r_hash);
                        right.hash = Some(l_hash);
                        let old_id = right.id;
                        // Here, we give the left item the new id to avoid a collision in the right set
                        right.id = left.id;
                        SomeLeft(
                            self.left_set
                                .remove_entry(rp_hash, hash_and_id(r_hash, old_id))
                                .unwrap()
                                .extract(),
                        )
                    }
                    (Some(lp_hash), Some(rp_hash)) => {
                        left.hash = Some(r_hash);
                        right.hash = Some(l_hash);
                        let old_l_id = left.id;
                        let old_r_id = right.id;
                        // Here, we give the pair a new id to avoid collisions in both sets
                        left.id = self.counter;
                        right.id = self.counter;
                        self.counter += 1;
                        SomeBoth(
                            self.left_set
                                .remove_entry(rp_hash, just_id(old_r_id))
                                .unwrap()
                                .extract(),
                            self.right_set
                                .remove_entry(lp_hash, just_id(old_l_id))
                                .unwrap()
                                .extract(),
                        )
                    }
                }
            }
            _ => Neither,
        }
    }

    /// Unpairs two existing items in the map. Returns `true` if they were successfully unpaired.
    /// Returns `false` if either item can not be found or if they aren't paired.
    pub fn unpair(&mut self, left: &L, right: &R) -> bool {
        let l_hash = make_hash::<L, S>(&self.hash_builder, left);
        let r_hash = make_hash::<R, S>(&self.hash_builder, right);
        let opt_left = self.left_set.get_mut(l_hash, equivalent_key(left));
        let opt_right = self.right_set.get_mut(r_hash, equivalent_key(right));
        match (opt_left, opt_right) {
            (Some(left), Some(right)) => match (left.hash, right.hash) {
                (Some(l_h), Some(r_h)) => {
                    if l_hash == r_h && r_hash == l_h {
                        left.hash = None;
                        right.hash = None;
                        right.id = self.counter;
                        self.counter += 1;
                        true
                    } else {
                        false
                    }
                }
                _ => false,
            },
            _ => false,
        }
    }

    /// Determines if an item in the left set is paired.
    ///
    /// Returns false if the item isn't found or is unpaired. Returns true otherwise.
    pub fn is_left_paired(&self, left: &L) -> bool {
        let l_hash = make_hash::<L, S>(&self.hash_builder, left);
        let opt_left = self.left_set.get(l_hash, equivalent_key(left));
        match opt_left {
            Some(l) => l.hash.is_some(),
            None => false,
        }
    }

    /// Determines if an item in the right set is paired.
    ///
    /// Returns false if the item isn't found or is unpaired. Returns true otherwise.
    pub fn is_right_paired(&self, right: &R) -> bool {
        let r_hash = make_hash::<R, S>(&self.hash_builder, right);
        let opt_right = self.right_set.get(r_hash, equivalent_key(right));
        match opt_right {
            Some(r) => r.hash.is_some(),
            None => false,
        }
    }

    /// Returns `true` if both items are in the map and are paired together; otherwise, returns
    /// `false`.
    pub fn are_paired(&self, left: &L, right: &R) -> bool {
        let l_hash = make_hash::<L, S>(&self.hash_builder, left);
        let r_hash = make_hash::<R, S>(&self.hash_builder, right);
        let opt_left = self.left_set.get(l_hash, equivalent_key(left));
        let opt_right = self.right_set.get(r_hash, equivalent_key(right));
        match (opt_left, opt_right) {
            (Some(left), Some(right)) => {
                left.id == right.id && Some(l_hash) == right.hash && Some(r_hash) == left.hash
            }
            _ => false,
        }
    }

    /// Returns `true` if the item is found and `false` otherwise.
    pub fn contains_left(&self, left: &L) -> bool {
        let hash = make_hash::<L, S>(&self.hash_builder, left);
        self.left_set.get(hash, equivalent_key(left)).is_some()
    }

    /// Returns `true` if the item is found and `false` otherwise.
    pub fn contains_right(&self, right: &R) -> bool {
        let hash = make_hash::<R, S>(&self.hash_builder, right);
        self.right_set.get(hash, equivalent_key(right)).is_some()
    }

    /// Removes and returns the give pair from the map provided that they are paired together.
    pub fn remove(&mut self, left: &L, right: &R) -> Option<(MappingPair<L>, MappingPair<R>)> {
        if self.are_paired(left, right) {
            let l = self.remove_left(left).unwrap();
            let r = self.remove_right(right).unwrap();
            Some((l, r))
        } else {
            None
        }
    }

    /// Removes and returns the given item from the left set and unpairs its associated item if it
    /// is paired.
    ///
    /// Note: If it exists, the associated right pairing is unchanged here.
    pub fn remove_left(&mut self, item: &L) -> Option<MappingPair<L>> {
        let l_hash = make_hash::<L, S>(&self.hash_builder, item);
        self.left_set.remove_entry(l_hash, equivalent_key(item))
    }

    /// Removes and returns the given item from the right set using a left item.
    ///
    /// Note: The left pairing is unchanged here.
    pub fn remove_via_left(&mut self, item: &L) -> Option<MappingPair<R>> {
        let l_hash = make_hash::<L, S>(&self.hash_builder, item);
        let left_pairing = self.left_set.get(l_hash, equivalent_key(item))?;
        self.right_set.remove_entry(
            *left_pairing.hash.as_ref()?,
            hash_and_id(l_hash, left_pairing.id),
        )
    }

    /// Removes and returns the given item from the left set and unpairs its associated item if it
    /// is paired.
    ///
    /// Note: If it exists, the associated left pairing is unchanged here.
    pub fn remove_right(&mut self, item: &R) -> Option<MappingPair<R>> {
        let r_hash = make_hash::<R, S>(&self.hash_builder, item);
        self.right_set.remove_entry(r_hash, equivalent_key(item))
    }

    /// Removes and returns the given item from the left set using a right item.
    ///
    /// Note: The left pairing is unchanged here.
    pub fn remove_via_right(&mut self, item: &R) -> Option<MappingPair<L>> {
        let r_hash = make_hash::<R, S>(&self.hash_builder, item);
        let right_pairing = self.right_set.get(r_hash, equivalent_key(item))?;
        self.left_set.remove_entry(
            *right_pairing.hash.as_ref()?,
            hash_and_id(r_hash, right_pairing.id),
        )
    }

    /// Removes a pair using the hash of the left item, right item, and their shared pairing id
    pub fn remove_via_hashes_and_id(
        &mut self,
        l_hash: u64,
        r_hash: u64,
        id: u64,
    ) -> OptionalPair<MappingPair<L>, MappingPair<R>> {
        let left_opt = self.left_set.remove_entry(l_hash, hash_and_id(r_hash, id));
        let right_opt = self.right_set.remove_entry(r_hash, hash_and_id(l_hash, id));
        OptionalPair::from((left_opt, right_opt))
    }

    /// Gets a reference to an item in the left set using an item in the right set.
    pub fn get_left(&self, item: &R) -> Option<&MappingPair<L>> {
        let r_hash = make_hash::<R, S>(&self.hash_builder, item);
        let right_pairing: &MappingPair<R> = self.get_right_inner_with_hash(item, r_hash)?;
        let hash = right_pairing.hash?;
        self.left_set
            .get(hash, hash_and_id(r_hash, right_pairing.id))
    }

    /// Gets a reference to an item in the left set using an item in the right set.
    pub fn get_left_mut(&mut self, item: &R) -> Option<&mut MappingPair<L>> {
        let r_hash = make_hash::<R, S>(&self.hash_builder, item);
        let right_pairing: &MappingPair<R> = self.get_right_inner_with_hash(item, r_hash)?;
        let hash = right_pairing.hash?;
        self.left_set
            .get_mut(hash, hash_and_id(r_hash, right_pairing.id))
    }

    /// Gets a reference to an item in the right set using an item in the left set.
    pub fn get_right(&self, item: &L) -> Option<&MappingPair<R>> {
        let l_hash = make_hash::<L, S>(&self.hash_builder, item);
        let left_pairing: &MappingPair<L> = self.get_left_inner_with_hash(item, l_hash)?;
        let hash = left_pairing.hash?;
        self.right_set
            .get(hash, hash_and_id(l_hash, left_pairing.id))
    }

    /// Gets a reference to an item in the right set using an item in the left set.
    pub fn get_right_mut(&mut self, item: &L) -> Option<&mut MappingPair<R>> {
        let l_hash = make_hash::<L, S>(&self.hash_builder, item);
        let left_pairing: &MappingPair<L> = self.get_left_inner_with_hash(item, l_hash)?;
        let hash = left_pairing.hash?;
        self.right_set
            .get_mut(hash, hash_and_id(l_hash, left_pairing.id))
    }

    /// Gets the bucket of an item in the right set using an item in the left set.
    fn find_right(&self, item: &MappingPair<L>) -> Option<Bucket<MappingPair<R>>> {
        let hash = item.hash?;
        self.right_set.find(hash, just_id(item.id))
    }

    /// Gets references to a pair using the hash of the left item, right item, and their
    /// shared pairing id
    pub fn get_via_hashes_and_id(
        &self,
        l_hash: u64,
        r_hash: u64,
        id: u64,
    ) -> Option<(&MappingPair<L>, &MappingPair<R>)> {
        let left_pairing = self.left_set.get(l_hash, hash_and_id(r_hash, id))?;
        let right_pairing = self.right_set.get(r_hash, hash_and_id(l_hash, id))?;
        Some((left_pairing, right_pairing))
    }

    /// Gets mutable references to a pair using the hash of the left item, right item, and their
    /// shared pairing id
    pub fn get_via_hashes_and_id_mut(
        &mut self,
        l_hash: u64,
        r_hash: u64,
        id: u64,
    ) -> Option<(&mut MappingPair<L>, &mut MappingPair<R>)> {
        let left_pairing = self.left_set.get_mut(l_hash, hash_and_id(r_hash, id))?;
        let right_pairing = self.right_set.get_mut(r_hash, hash_and_id(l_hash, id))?;
        Some((left_pairing, right_pairing))
    }

    #[inline]
    /// Gets a left pairing with a left item
    pub fn get_left_inner(&self, item: &L) -> Option<&MappingPair<L>> {
        let hash = make_hash::<L, S>(&self.hash_builder, item);
        self.left_set.get(hash, equivalent_key(item))
    }

    #[inline]
    /// Gets a left pairing with a left item and its hash
    pub fn get_left_inner_with_hash(&self, item: &L, hash: u64) -> Option<&MappingPair<L>> {
        self.left_set.get(hash, equivalent_key(item))
    }

    #[inline]
    /// Gets a right pairing with a right item
    pub fn get_right_inner(&self, item: &R) -> Option<&MappingPair<R>> {
        let hash = make_hash::<R, S>(&self.hash_builder, item);
        self.right_set.get(hash, equivalent_key(item))
    }

    #[inline]
    /// Gets a right pairing with a right item and its hash
    pub fn get_right_inner_with_hash(&self, item: &R, hash: u64) -> Option<&MappingPair<R>> {
        self.right_set.get(hash, equivalent_key(item))
    }

    /// Returns an iterator over the items in the map
    pub fn iter(&self) -> Iter<'_, L, R, S> {
        Iter {
            left_iter: unsafe { self.left_set.iter() },
            right_iter: unsafe { self.right_set.iter() },
            map_ref: self,
        }
    }

    /// Returns an iterator over the pairs in the map
    pub fn iter_paired(&self) -> PairedIter<'_, L, R, S> {
        PairedIter {
            left_iter: unsafe { self.left_set.iter() },
            map_ref: self,
        }
    }

    /// Returns an iterator over the unpaired items in the map
    ///
    /// Nope: The iterator will never yield the `Neither` nor `SomeBoth` variants of
    /// `OptionalPair`.
    pub fn iter_unpaired(&self) -> UnpairedIter<'_, L, R, S> {
        UnpairedIter {
            left_iter: unsafe { self.left_set.iter() },
            right_iter: unsafe { self.right_set.iter() },
            map_ref: self,
        }
    }

    /// Returns an iterator over elements in the left set
    pub fn iter_left(&self) -> SingleIter<'_, L> {
        SingleIter {
            iter: unsafe { self.left_set.iter() },
            marker: PhantomData,
        }
    }

    /// Returns an iterator over elements in the right set
    pub fn iter_right(&self) -> SingleIter<'_, R> {
        SingleIter {
            iter: unsafe { self.right_set.iter() },
            marker: PhantomData,
        }
    }

    /// Clears the map, returning all items as an iterator while keeping the backing memory
    /// allocated for reuse. If the returned iterator is dropped before being fully consumed, it
    /// drops the remaining pairs.
    pub fn drain(&mut self) -> DrainIter<'_, L, R> {
        DrainIter {
            left_iter: self.left_set.drain(),
            right_ref: &mut self.right_set,
        }
    }

    /// Returns an iterator that removes and yields all items that evaluate to `true` in the given
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
    pub fn drain_filter<F>(&mut self, f: F) -> DrainFilterIter<'_, L, R, F>
    where
        F: FnMut(OptionalPair<&L, &R>) -> bool,
    {
        unsafe {
            DrainFilterIter {
                f,
                inner: DrainFilterInner {
                    left_iter: self.left_set.iter(),
                    right_iter: self.right_set.iter(),
                    left_ref: &mut self.left_set,
                    right_ref: &mut self.right_set,
                    reset_right_iter: true,
                },
            }
        }
    }

    /// Shrinks the capacity of the left set with a lower limit. It will drop down no lower than the
    /// supplied limit while maintaining the internal rules and possibly leaving some space in
    /// accordance with the resize policy.
    ///
    /// This function does nothing if the current capacity is smaller than the supplied minimum capacity.
    pub fn shrink_to_left(&mut self, min_capacity: usize) {
        self.left_set
            .shrink_to(min_capacity, make_hasher(&self.hash_builder));
    }

    /// Shrinks the capacity of the right set with a lower limit. It will drop down no lower than the
    /// supplied limit while maintaining the internal rules and possibly leaving some space in
    /// accordance with the resize policy.
    ///
    /// This function does nothing if the current capacity is smaller than the supplied minimum capacity.
    pub fn shrink_to_right(&mut self, min_capacity: usize) {
        self.right_set
            .shrink_to(min_capacity, make_hasher(&self.hash_builder));
    }

    /// Shrinks the capacity of the map as much as possible. It will drop down as much as possible
    /// while maintaining the internal rules and possibly leaving some space in accordance with the
    /// resize policy.
    pub fn shrink_to_fit(&mut self) {
        self.left_set
            .shrink_to(self.len_left(), make_hasher(&self.hash_builder));
        self.right_set
            .shrink_to(self.len_right(), make_hasher(&self.hash_builder));
    }

    /// Reserves capacity for at least additional more elements to be inserted in the HashMap. The
    /// collection may reserve more space to avoid frequent reallocations.
    ///
    /// # Panics
    /// Panics if the new allocation size overflows usize.
    pub fn reserve_left(&mut self, additional: usize) {
        self.left_set
            .reserve(additional, make_hasher(&self.hash_builder));
    }

    /// Reserves capacity for at least additional more elements to be inserted in the HashMap. The
    /// collection may reserve more space to avoid frequent reallocations.
    ///
    /// # Panics
    /// Panics if the new allocation size overflows usize.
    pub fn reserve_right(&mut self, additional: usize) {
        self.right_set
            .reserve(additional, make_hasher(&self.hash_builder));
    }

    /// Tries to reserve capacity for at least additional more elements to be inserted in the given
    /// `HashMap<K,V>`. The collection may reserve more space to avoid frequent reallocations.
    ///
    /// # Errors
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    pub fn try_reserve_left(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.left_set
            .try_reserve(additional, make_hasher(&self.hash_builder))?;
        Ok(())
    }

    /// Tries to reserve capacity for at least additional more elements to be inserted in the given
    /// `HashMap<K,V>`. The collection may reserve more space to avoid frequent reallocations.
    ///
    /// # Errors
    /// If the capacity overflows, or the allocator reports a failure, then an error is returned.
    pub fn try_reserve_right(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.right_set
            .try_reserve(additional, make_hasher(&self.hash_builder))?;
        Ok(())
    }
}

impl<L, R, S> Clone for RawCycleMap<L, R, S>
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

impl<L, R, S> Default for RawCycleMap<L, R, S>
where
    S: Default,
{
    fn default() -> Self {
        Self::with_hasher(Default::default())
    }
}

impl<L, R, S> fmt::Debug for RawCycleMap<L, R, S>
where
    L: Hash + Eq + fmt::Debug,
    R: Hash + Eq + fmt::Debug,
    S: BuildHasher,
{
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_set()
            .entries(self.iter().map(|op| op.map(|l| l.as_ptr(), |r| r.as_ptr())))
            .finish()
    }
}

impl<L, R, S> RawCycleMap<L, R, S> {
    /// Creates a `RawCycleMap`and that uses the given hasher.
    ///
    /// Warning: `hash_builder` is normally randomly generated, and is designed to allow
    /// `RawCycleMap`s to be resistant to attacks that cause many collisions and very poor
    /// performance. Setting it manually using this function can expose a DoS attack vector.
    ///
    /// The `hash_builder` passed should implement the [`BuildHasher`] trait for the CycleMap to be
    /// useful, see its documentation for details.
    pub const fn with_hasher(hash_builder: S) -> Self {
        Self {
            hash_builder,
            counter: 0,
            left_set: RawTable::new(),
            right_set: RawTable::new(),
        }
    }

    /// Creates a `RawCycleMap` with inner sets that have at least the specified capacity, and that
    /// uses the given hasher.
    ///
    /// The map will be able to hold at least `capacity` many pairs before reallocating.
    ///
    /// Warning: `hash_builder` is normally randomly generated, and is designed to allow
    /// `RawCycleMap`s to be resistant to attacks that cause many collisions and very poor
    /// performance. Setting it manually using this function can expose a DoS attack vector.
    ///
    /// The `hash_builder` passed should implement the [`BuildHasher`] trait for the CycleMap to be
    /// useful, see its documentation for details.
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
    pub fn capacity_left(&self) -> usize {
        // The size of the sets is always equal
        self.left_set.capacity()
    }

    /// Returns the number of items that the right set can hold without reallocation.
    pub fn capacity_right(&self) -> usize {
        // The size of the sets is always equal
        self.right_set.capacity()
    }

    /// Returns the len of the inner sets (same between sets)
    pub fn len_left(&self) -> usize {
        self.left_set.len()
    }

    /// Returns the len of the inner sets (same between sets)
    pub fn len_right(&self) -> usize {
        self.right_set.len()
    }

    /// Returns true if no items are in the map and false otherwise
    pub fn is_empty(&self) -> bool {
        self.len_left() + self.len_right() == 0
    }

    /// Removes all items for the map while keeping the backing memory allocated for reuse.
    pub fn clear(&mut self) {
        self.left_set.clear();
        self.right_set.clear();
    }
}

impl<L, R, S> Extend<(L, R)> for RawCycleMap<L, R, S>
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

impl<L, R, S> Extend<OptionalPair<L, R>> for RawCycleMap<L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
    #[inline]
    fn extend<T: IntoIterator<Item = OptionalPair<L, R>>>(&mut self, iter: T) {
        for op in iter {
            match op {
                Neither => {}
                SomeLeft(l) => {
                    self.insert_left(l);
                }
                SomeRight(r) => {
                    self.insert_right(r);
                }
                SomeBoth(l, r) => {
                    self.insert(l, r);
                }
            }
        }
    }
}

impl<L, R> FromIterator<(L, R)> for RawCycleMap<L, R>
where
    L: Hash + Eq,
    R: Hash + Eq,
{
    fn from_iter<T: IntoIterator<Item = (L, R)>>(iter: T) -> Self {
        let mut digest = RawCycleMap::default();
        digest.extend(iter);
        digest
    }
}

impl<L, R> FromIterator<OptionalPair<L, R>> for RawCycleMap<L, R>
where
    L: Hash + Eq,
    R: Hash + Eq,
{
    fn from_iter<T: IntoIterator<Item = OptionalPair<L, R>>>(iter: T) -> Self {
        let mut digest = RawCycleMap::default();
        digest.extend(iter);
        digest
    }
}

/// An iterator over the entry items of a `RawCycleMap`.
pub struct Iter<'a, L, R, S> {
    left_iter: RawIter<MappingPair<L>>,
    right_iter: RawIter<MappingPair<R>>,
    map_ref: &'a RawCycleMap<L, R, S>,
}

impl<L, R, S> Clone for Iter<'_, L, R, S> {
    fn clone(&self) -> Self {
        Self {
            left_iter: self.left_iter.clone(),
            right_iter: self.right_iter.clone(),
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
        f.debug_list()
            .entries(
                self.clone()
                    .map(|op| op.map(|l| l.as_ptr(), |r| r.as_ptr())),
            )
            .finish()
    }
}

impl<'a, L, R, S> Iterator for Iter<'a, L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
    type Item = OptionalPair<Bucket<MappingPair<L>>, Bucket<MappingPair<R>>>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.left_iter.next() {
            Some(l) => match self.map_ref.find_right(unsafe { l.as_ref() }) {
                Some(r) => Some(OptionalPair::SomeBoth(l, r)),
                None => Some(OptionalPair::SomeLeft(l)),
            },
            None => match self.right_iter.next() {
                Some(r) => Some(OptionalPair::SomeRight(r)),
                None => None,
            },
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.left_iter.size_hint()
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

/// An iterator over the entry pairs of a `RawCycleMap`.
pub struct PairedIter<'a, L, R, S> {
    left_iter: RawIter<MappingPair<L>>,
    map_ref: &'a RawCycleMap<L, R, S>,
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
        f.debug_list()
            .entries(self.clone().map(|(l, r)| (l.as_ptr(), r.as_ptr())))
            .finish()
    }
}

impl<'a, L, R, S> Iterator for PairedIter<'a, L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
    type Item = (Bucket<MappingPair<L>>, Bucket<MappingPair<R>>);

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(l_pairing) = self.left_iter.next() {
            // Ignore all unpaired items
            let l = unsafe { l_pairing.as_ref() };
            if l.hash.is_none() {
                continue;
            }
            match self.map_ref.find_right(l) {
                Some(r) => {
                    return Some((l_pairing, r));
                }
                None => { // TODO: This shouldn't happen, but what if it does...
                    continue;
                }
            };
        }
        None
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

/// An iterator over the entry pairs of a `RawCycleMap`.
pub struct UnpairedIter<'a, L, R, S> {
    left_iter: RawIter<MappingPair<L>>,
    right_iter: RawIter<MappingPair<R>>,
    map_ref: &'a RawCycleMap<L, R, S>,
}

impl<L, R, S> Clone for UnpairedIter<'_, L, R, S> {
    fn clone(&self) -> Self {
        Self {
            left_iter: self.left_iter.clone(),
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
        f.debug_list()
            .entries(
                self.clone()
                    .map(|op| op.map(|l| l.as_ptr(), |r| r.as_ptr())),
            )
            .finish()
    }
}

impl<'a, L, R, S> Iterator for UnpairedIter<'a, L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
    type Item = OptionalPair<Bucket<MappingPair<L>>, Bucket<MappingPair<R>>>;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(l) = self.left_iter.next() {
            // Ignore all paired items
            if unsafe { l.as_ref().hash.is_some() } {
                continue;
            }
            return Some(SomeLeft(l));
        }
        while let Some(r) = self.right_iter.next() {
            // Ignore all paired items
            if unsafe { r.as_ref().hash.is_some() } {
                continue;
            }
            return Some(SomeRight(r));
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.left_iter.size_hint()
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

/// An iterator over the elements of an inner set of a `RawCycleMap`.
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
        f.debug_list().entries(self.clone().map(|m| m.as_ptr())).finish()
    }
}

impl<'a, T> Iterator for SingleIter<'a, T>
where
    T: 'a + Hash + Eq,
{
    type Item = Bucket<MappingPair<T>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
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

/// An iterator over the entry pairs of a `RawCycleMap`.
#[allow(missing_debug_implementations)]
pub struct DrainIter<'a, L, R>
where
    L: Eq + Hash,
    R: Eq + Hash,
{
    left_iter: RawDrain<'a, MappingPair<L>>,
    right_ref: &'a mut RawTable<MappingPair<R>>,
}

impl<'a, L, R> Drop for DrainIter<'a, L, R>
where
    L: Eq + Hash,
    R: Eq + Hash,
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

impl<'a, L, R> Iterator for DrainIter<'a, L, R>
where
    L: Hash + Eq,
    R: Hash + Eq,
{
    type Item = OptionalPair<L, R>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.left_iter.next() {
            // Not done with the left set yet
            Some(left) => match left.hash {
                Some(hash) => {
                    let right = self
                        .right_ref
                        .remove_entry(hash, just_id(left.id))
                        .unwrap()
                        .extract();
                    Some(SomeBoth(left.extract(), right))
                }
                None => Some(SomeLeft(left.extract())),
            },
            None => match self.right_ref.drain().next() {
                Some(right) => Some(SomeRight(right.extract())),
                None => None,
            },
        }
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
    L: Eq,
    R: Eq,
    F: FnMut(OptionalPair<&L, &R>) -> bool,
{
    f: F,
    inner: DrainFilterInner<'a, L, R>,
}

impl<'a, L, R, F> Drop for DrainFilterIter<'a, L, R, F>
where
    L: Eq,
    R: Eq,
    F: FnMut(OptionalPair<&L, &R>) -> bool,
{
    fn drop(&mut self) {
        while let Some(item) = self.next() {
            let guard = ConsumeAllOnDrop(self);
            drop(item);
            mem::forget(guard);
        }
    }
}

impl<L: Eq, R: Eq, F> Iterator for DrainFilterIter<'_, L, R, F>
where
    F: FnMut(OptionalPair<&L, &R>) -> bool,
{
    type Item = OptionalPair<L, R>;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next(&mut self.f)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, self.inner.left_iter.size_hint().1)
    }
}

impl<L: Eq, R: Eq, F> FusedIterator for DrainFilterIter<'_, L, R, F> where
    F: FnMut(OptionalPair<&L, &R>) -> bool
{
}

/// Portions of `DrainFilter` shared with `set::DrainFilter`
pub(super) struct DrainFilterInner<'a, L, R> {
    pub(super) left_iter: RawIter<MappingPair<L>>,
    pub(super) right_iter: RawIter<MappingPair<R>>,
    pub(super) left_ref: &'a mut RawTable<MappingPair<L>>,
    pub(super) right_ref: &'a mut RawTable<MappingPair<R>>,
    pub(super) reset_right_iter: bool,
}

impl<L: Eq, R: Eq> DrainFilterInner<'_, L, R> {
    pub(super) fn next<F>(&mut self, f: &mut F) -> Option<OptionalPair<L, R>>
    where
        F: FnMut(OptionalPair<&L, &R>) -> bool,
    {
        while let Some(left) = self.left_iter.next() {
            let l_pairing = unsafe { left.as_ref() };
            match l_pairing.hash {
                Some(hash) => {
                    let right = self.right_ref.find(hash, just_id(l_pairing.id)).unwrap();
                    if unsafe { f(SomeBoth(&l_pairing.value, &right.as_ref().value)) } {
                        let l = unsafe { self.left_ref.remove(left).extract() };
                        let r = unsafe { self.right_ref.remove(right).extract() };
                        return Some(SomeBoth(l, r));
                    }
                }
                None => {
                    if f(SomeLeft(&l_pairing.value)) {
                        let l = unsafe { self.left_ref.remove(left).extract() };
                        return Some(SomeLeft(l));
                    }
                }
            }
        }
        if self.reset_right_iter {
            self.right_iter = unsafe { self.right_ref.iter() };
            self.reset_right_iter = false;
        }
        while let Some(right) = self.right_iter.next() {
            let r_pairing = unsafe { right.as_ref() };
            if f(SomeRight(&r_pairing.value)) {
                let r = unsafe { self.right_ref.remove(right).extract() };
                return Some(SomeRight(r));
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
            "MappingPair {{ value: {:?}, hash: {:?}, id: {} }}",
            self.value, self.hash, self.id
        )
    }
}
