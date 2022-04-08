use std::{
    default::Default,
    fmt,
    hash::{BuildHasher, Hash},
    iter::FusedIterator,
    marker::PhantomData,
};

use hashbrown::{
    hash_map::DefaultHashBuilder,
    raw::{RawIter, RawTable},
};

use crate::optionals::*;
use crate::utils::*;

// Contains a value and the hash of the item that the value maps to.
pub(crate) struct MappingPair<T> {
    pub(crate) value: T,
    pub(crate) hash: Option<u64>,
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
    move |x| id == x.id && Some(hash) == x.hash
}

/// Similar to [`CycleMap`] but items might be not paired.
///
/// [`CycleMap`]: crate.struct.CycleMap.html
pub struct PartialCycleMap<L, R, St = DefaultHashBuilder> {
    pub(crate) hash_builder: St,
    pub(crate) counter: u64,
    left_set: RawTable<MappingPair<L>>,
    right_set: RawTable<MappingPair<R>>,
}

impl<L, R> PartialCycleMap<L, R, DefaultHashBuilder> {
    #[inline]
    /// Creates a new PartialCycleMap
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
    /// Creates a new PartialCycleMap whose inner sets each of the given capacity
    pub fn with_capacity(capacity: usize) -> Self {
        Self::with_capacity_and_hasher(capacity, DefaultHashBuilder::default())
    }
}

impl<L, R, S> PartialCycleMap<L, R, S>
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
    pub fn insert(&mut self, left: L, right: R) -> (OptionalPair<L, R>, OptionalPair<L, R>) {
        let opt_from_left = self.remove_via_left(&left);
        let opt_from_right = self.remove_via_right(&right);
        let digest = (opt_from_left, opt_from_right);
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
        digest
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
                left.id == right.id && Some(l_hash) == right.hash && Some(r_hash) == left.hash
            }
            _ => false,
        }
    }

    /// Removes a pair of items only if they are mapped together and returns the pair
    pub fn remove(&mut self, left: &L, right: &R) -> Option<(L, R)> {
        if self.are_mapped(left, right) {
            Option::from(self.remove_via_left(left))
                .map(|(opt_l, opt_r)| (opt_l.unwrap(), opt_r.unwrap()))
        } else {
            None
        }
    }

    /// Removes the given item from the left set and its associated item from the right set
    pub fn remove_via_left(&mut self, item: &L) -> OptionalPair<L, R> {
        let l_hash = make_hash::<L, S>(&self.hash_builder, item);
        let left_pairing: MappingPair<L> =
            if let Some(p) = self.left_set.remove_entry(l_hash, equivalent_key(item)) {
                p
            } else {
                return OptionalPair::None;
            };
        let right_value: Option<R> = if let Some(hash) = left_pairing.hash {
            Some(
                self.right_set
                    .remove_entry(hash, hash_and_id(l_hash, left_pairing.id))
                    .unwrap()
                    .extract(),
            )
        } else {
            None
        };
        OptionalPair::from((Some(left_pairing.extract()), right_value))
    }

    /// Removes the given item from the right set and its associated item from the left set
    pub fn remove_via_right(&mut self, item: &R) -> OptionalPair<L, R> {
        let r_hash = make_hash::<R, S>(&self.hash_builder, item);
        let right_pairing: MappingPair<R> =
            if let Some(p) = self.right_set.remove_entry(r_hash, equivalent_key(item)) {
                p
            } else {
                return OptionalPair::None;
            };
        let left_value: Option<L> = if let Some(hash) = right_pairing.hash {
            Some(
                self.left_set
                    .remove_entry(hash, hash_and_id(r_hash, right_pairing.id))
                    .unwrap()
                    .extract(),
            )
        } else {
            None
        };
        OptionalPair::from((left_value, Some(right_pairing.extract())))
    }

    /// Removes a pair using the hash of the left item, right item, and their shared pairing id
    fn remove_via_hashes_and_id(
        &mut self,
        l_hash: u64,
        r_hash: u64,
        id: u64,
    ) -> OptionalPair<L, R> {
        let left_opt = self
            .left_set
            .remove_entry(l_hash, hash_and_id(r_hash, id))
            .map(|opt_l| opt_l.extract());
        let right_opt = self
            .right_set
            .remove_entry(r_hash, hash_and_id(l_hash, id))
            .map(|opt_r| opt_r.extract());
        OptionalPair::from((left_opt, right_opt))
    }

    /// Swaps an item in the left set with another item, remaps the old item's associated right
    /// item, and returns the old left item.
    ///
    /// If there is another item in the left set that is equal to the new left item which is mapped
    /// to another right item, that cycle is removed.
    ///
    /// Note: This method will never return the `SomeRight` variant of `OptionalPair`.
    ///
    /// If there is a collision, the old cycle is returned.
    pub fn swap_left(&mut self, old: &L, new: L) -> OptionalPair<L, OptionalPair<L, R>> {
        // Check for Eq left item and remove that cycle if it exists
        let new_l_hash = make_hash::<L, S>(&self.hash_builder, &new);
        let eq_opt = self.swap_left_eq_check(old, &new, new_l_hash);
        // Find the old left pairing
        let old_l_hash = make_hash::<L, S>(&self.hash_builder, old);
        let l_pairing: &MappingPair<L> = match self.left_set.get(old_l_hash, equivalent_key(old)) {
            Some(p) => p,
            None => {
                return OptionalPair::None;
            }
        };
        if let Some(hash) = l_pairing.hash {
            // Use old left pairing to find right pairing
            let r_pairing: &mut MappingPair<R> = self
                .right_set
                .get_mut(hash, hash_and_id(old_l_hash, l_pairing.id))
                .unwrap();
            // Updated right pairing
            r_pairing.hash = Some(new_l_hash);
        }
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
        if eq_opt.is_none() {
            OptionalPair::SomeLeft(old_left_item)
        } else {
            OptionalPair::SomeBoth(old_left_item, eq_opt)
        }
    }

    /// Does what [`swap_left`] does, but fails to swap and returns None if the old item isn't
    /// mapped to the given right item.
    ///
    /// [`swap_left`]: struct.PartialCycleMap.html#method.swap_left
    pub fn swap_left_checked(
        &mut self,
        old: &L,
        expected: &R,
        new: L,
    ) -> OptionalPair<L, OptionalPair<L, R>> {
        // Check if old and expected are mapped
        if !self.are_mapped(old, expected) {
            return OptionalPair::None;
        }
        self.swap_left(old, new)
    }

    /// Does what [`swap_left`] does, but inserts a new pair if the old left item isn't in the map.
    /// None is returned on insert.
    ///
    /// [`swap_left`]: struct.PartialCycleMap.html#method.swap_left
    pub fn swap_left_or_insert(
        &mut self,
        old: &L,
        new: L,
        to_insert: R,
    ) -> OptionalPair<L, OptionalPair<L, R>> {
        let old_l_hash = make_hash::<L, S>(&self.hash_builder, old);
        if self.left_set.get(old_l_hash, equivalent_key(old)).is_some() {
            self.swap_left(old, new)
        } else {
            // TODO: Do further verification on this. All cases _should_ be covered here
            match self.insert(new, to_insert) {
                (OptionalPair::None, OptionalPair::None) => OptionalPair::None,
                (OptionalPair::None, pair) => OptionalPair::SomeRight(pair),
                _ => {
                    unreachable!("There isn't a left item")
                }
            }
        }
    }

    /// Pair of the collision checks done in the swap left methods
    fn swap_left_eq_check(&mut self, old: &L, new: &L, new_hash: u64) -> OptionalPair<L, R> {
        let opt = self.left_set.get(new_hash, equivalent_key(new));
        if opt.is_some() && new != old {
            // Remove the problem cycle
            self.remove_via_left(new)
        } else {
            // If old and new are the same, they we are updating an cycle
            OptionalPair::None
        }
    }

    /// Swaps an item in the right set with another item, remaps the old item's associated left
    /// item, and returns the old right item
    pub fn swap_right(&mut self, old: &R, new: R) -> OptionalPair<R, OptionalPair<L, R>> {
        // Check for Eq left item and remove that cycle if it exists
        let new_r_hash = make_hash::<R, S>(&self.hash_builder, &new);
        let eq_opt = self.swap_right_eq_check(old, &new, new_r_hash);
        // Find the old right pairing
        let old_r_hash = make_hash::<R, S>(&self.hash_builder, old);
        let r_pairing: &MappingPair<R> = match self.right_set.get(old_r_hash, equivalent_key(old)) {
            Some(p) => p,
            None => {
                return OptionalPair::None;
            }
        };
        if let Some(hash) = r_pairing.hash {
            // Use old right pairing to find the left pairing
            let l_pairing: &mut MappingPair<L> = self
                .left_set
                .get_mut(hash, hash_and_id(old_r_hash, r_pairing.id))
                .unwrap();
            // Updated left pairing
            l_pairing.hash = Some(new_r_hash);
        }
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
        if eq_opt.is_none() {
            OptionalPair::SomeLeft(old_right_item)
        } else {
            OptionalPair::SomeBoth(old_right_item, eq_opt)
        }
    }

    /// Does what [`swap_right`] does, but fails to swap if the old item isn't mapped to the given
    /// left item.
    ///
    /// [`swap_right`]: struct.PartialCycleMap.html#method.swap_right
    pub fn swap_right_checked(
        &mut self,
        old: &R,
        expected: &L,
        new: R,
    ) -> OptionalPair<R, OptionalPair<L, R>> {
        // Check if old and expected are mapped
        if !self.are_mapped(expected, old) {
            return OptionalPair::None;
        } // Things can be removed after this point
        self.swap_right(old, new)
    }

    /// Does what [`swap_right`] does, but inserts a new pair if the old right item isn't in the map
    /// None is returned on insert.
    ///
    /// [`swap_right`]: struct.PartialCycleMap.html#method.swap_right
    pub fn swap_right_or_insert(
        &mut self,
        old: &R,
        new: R,
        to_insert: L,
    ) -> OptionalPair<R, OptionalPair<L, R>> {
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
                (OptionalPair::None, OptionalPair::None) => OptionalPair::None,
                (pair, OptionalPair::None) => OptionalPair::SomeRight(pair),
                _ => {
                    unreachable!("There isn't a left item")
                }
            }
        }
    }

    /// Pair of the collision checks done in the swap left methods
    fn swap_right_eq_check(&mut self, old: &R, new: &R, new_hash: u64) -> OptionalPair<L, R> {
        let opt = self.right_set.get(new_hash, equivalent_key(new));
        if opt.is_some() && new != old {
            // Remove the problem cycle
            self.remove_via_right(new)
        } else {
            // If old and new are the same, they we are updating an cycle
            OptionalPair::None
        }
    }

    /// Gets a reference to an item in the left set using an item in the right set.
    pub fn get_left(&self, item: &R) -> Option<&L> {
        let r_hash = make_hash::<R, S>(&self.hash_builder, item);
        let right_pairing: &MappingPair<R> = self.get_right_inner_with_hash(item, r_hash)?;
        let hash = right_pairing.hash?;
        match self
            .left_set
            .get(hash, hash_and_id(r_hash, right_pairing.id))
        {
            None => None,
            Some(pairing) => Some(&pairing.value),
        }
    }

    /// Gets a reference to an item in the right set using an item in the left set.
    pub fn get_right(&self, item: &L) -> Option<&R> {
        let l_hash = make_hash::<L, S>(&self.hash_builder, item);
        let left_pairing: &MappingPair<L> = self.get_left_inner_with_hash(item, l_hash)?;
        let hash = left_pairing.hash?;
        match self
            .right_set
            .get(hash, hash_and_id(l_hash, left_pairing.id))
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
    fn get_right_inner(&self, item: &R) -> Option<&MappingPair<R>> {
        let hash = make_hash::<R, S>(&self.hash_builder, item);
        self.right_set.get(hash, equivalent_key(item))
    }

    #[inline]
    fn get_right_inner_with_hash(&self, item: &R, hash: u64) -> Option<&MappingPair<R>> {
        self.right_set.get(hash, equivalent_key(item))
    }

    /* Likely to be used in the Drain iterator
    /// Takes an item from the left set and returns it (if it exists).
    ///
    /// This method is unsafe since removing the item break a cycle in the map.
    /// Ensure that any element you remove this way has its corresponding item removed too.
    pub(crate) unsafe fn take_left(&mut self, item: &R) -> Option<MappingPair<L>> {
        let r_hash = make_hash::<R, S>(&self.hash_builder, item);
        let right_pairing: &MappingPair<R> = self.right_set.get(r_hash, equivalent_key(item))?;
        self.left_set
            .remove_entry(right_pairing.hash, hash_and_id(r_hash, right_pairing.id))
    }

    /// Takes an item from the right set and returns it (if it exists).
    ///
    /// This method is unsafe since removing the item break a cycle in the map.
    /// Ensure that any element you remove this way has its corresponding item removed too.
    pub(crate) unsafe fn take_right(&mut self, item: &L) -> Option<MappingPair<R>> {
        let l_hash = make_hash::<L, S>(&self.hash_builder, item);
        let left_pairing: &MappingPair<L> = self.left_set.get(l_hash, equivalent_key(item))?;
        self.right_set
            .remove_entry(left_pairing.hash, hash_and_id(l_hash, left_pairing.id))
    }
    */

    /// Returns an iterator over the items in the map
    pub fn iter(&self) -> Iter<'_, L, R, S> {
        Iter {
            left_iter: unsafe { self.left_set.iter() },
            map_ref: self,
        }
    }

    /// Returns an iterator over the paired items in the map
    pub fn iter_mapped(&self) -> MappedIter<'_, L, R, S> {
        MappedIter {
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
    
    /// Drops all pairs that cause the predicate to return `false` while keeping the backing memory
    /// allocated
    pub fn retain_mapped<F>(&mut self, mut f: F)
    where
        F: FnMut(&L, &R) -> bool,
    {
        let mut to_drop: Vec<(u64, u64, u64)> = Vec::with_capacity(self.left_set.len());
        for (left, right) in self.iter_mapped() {
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

    /// Drops all items that cause the predicate to return `false` while keeping the backing memory
    /// allocated
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&OptionalPair<&L, &R>) -> bool,
    {
        let mut to_drop: Vec<(Option<u64>, Option<u64>, u64)> =
            Vec::with_capacity(self.left_set.len());
        for op in self.iter() {
            if !f(&op) {
                let (left, right): (Option<&L>, Option<&R>) = op.into();
                let l_hash: Option<u64> = if left.is_some() {
                    Some(make_hash::<L, S>(&self.hash_builder, left.unwrap()))
                } else {
                    None
                };
                let r_hash: Option<u64> = if right.is_some() {
                    Some(make_hash::<R, S>(&self.hash_builder, right.unwrap()))
                } else {
                    None
                };
                let id = if left.is_some() {
                    self.get_left_inner(left.unwrap()).unwrap().id
                } else {
                    self.get_right_inner(right.unwrap()).unwrap().id
                };
                to_drop.push((l_hash, r_hash, id));
            }
        }
        for tup in to_drop {
            match tup {
                (Some(l), Some(r), id) => {
                    self.remove_via_hashes_and_id(l, r, id);
                }
                (Some(l), None, id) => {
                    self.left_set.remove_entry(l, |p| p.id == id);
                }
                (None, Some(r), id) => {
                    self.right_set.remove_entry(r, |p| p.id == id);
                }
                _ => {
                    unreachable!("There is either some left or some right hash.");
                }
            }
        }
    }
}

impl<L, R, S> Default for PartialCycleMap<L, R, S>
where
    S: Default,
{
    fn default() -> Self {
        Self::with_hasher(Default::default())
    }
}

impl<L, R, S> fmt::Debug for PartialCycleMap<L, R, S>
where
    L: Hash + Eq + fmt::Debug,
    R: Hash + Eq + fmt::Debug,
    S: BuildHasher,
{
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt.debug_set().entries(self.iter()).finish()
    }
}

impl<L, R, S> PartialEq<PartialCycleMap<L, R, S>> for PartialCycleMap<L, R, S>
where
    L: Hash + Eq + fmt::Debug,
    R: Hash + Eq + fmt::Debug,
    S: BuildHasher,
{
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }
        self.iter()
            .all(|op| 
                match op {
                    OptionalPair::SomeLeft(l) => {
                        other.get_right(l).is_none()
                    },
                    OptionalPair::SomeRight(r) => {
                        other.get_left(r).is_none()
                    },
                    OptionalPair::SomeBoth(l,r) => {
                        other.are_mapped(l, r)
                    },
                    _ => { unreachable!("There has to be at least one item.") }
                }
            )
    }
}

impl<L, R, S> Eq for PartialCycleMap<L, R, S>
where
    L: Hash + Eq + fmt::Debug,
    R: Hash + Eq + fmt::Debug,
    S: BuildHasher,
{
}

impl<L, R, S> PartialCycleMap<L, R, S> {
    /// Creates a PartialCycleMap that uses the given hasher
    pub const fn with_hasher(hash_builder: S) -> Self {
        Self {
            hash_builder,
            counter: 0,
            left_set: RawTable::new(),
            right_set: RawTable::new(),
        }
    }

    /// Creates a PartialCycleMap that uses the given hasher and whose inner sets each have the given capacity
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
    pub fn left_capacity(&self) -> usize {
        // The size of the sets is always equal
        self.left_set.capacity()
    }

    /// Returns the capacity of the right set
    pub fn right_capacity(&self) -> usize {
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
    pub fn len(&self) -> usize {
        // The size of the sets is always equal
        self.left_set.len()
    }

    /// Returns true if no items are in the map and false otherwise
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Removes all pairs for the set while keeping the backing memory allocated
    pub fn clear(&mut self) {
        self.left_set.clear();
        self.right_set.clear();
    }
}

impl<L, R, S> Extend<(L, R)> for PartialCycleMap<L, R, S>
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

impl<L, R> FromIterator<(L, R)> for PartialCycleMap<L, R>
where
    L: Hash + Eq,
    R: Hash + Eq,
{
    fn from_iter<T: IntoIterator<Item = (L, R)>>(iter: T) -> Self {
        let mut digest = PartialCycleMap::default();
        digest.extend(iter);
        digest
    }
}

/// An iterator over the entry items of a `PartialCycleMap`.
pub struct Iter<'a, L, R, S> {
    left_iter: RawIter<MappingPair<L>>,
    map_ref: &'a PartialCycleMap<L, R, S>,
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
    type Item = OptionalPair<&'a L, &'a R>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.left_iter.next() {
            Some(l) => unsafe {
                let left = &l.as_ref().value;
                let right = self.map_ref.get_right(left);
                Some(OptionalPair::from((Some(left), right)))
            },
            None => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.left_iter.size_hint()
    }
}

impl<L, R, S> FusedIterator for Iter<'_, L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
}

/// An iterator over the entry pairs of a `PartialCycleMap`.
pub struct MappedIter<'a, L, R, S> {
    left_iter: RawIter<MappingPair<L>>,
    right_iter: RawIter<MappingPair<R>>,
    map_ref: &'a PartialCycleMap<L, R, S>,
}

impl<L, R, S> Clone for MappedIter<'_, L, R, S> {
    fn clone(&self) -> Self {
        Self {
            left_iter: self.left_iter.clone(),
            right_iter: self.right_iter.clone(),
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
        // Ignore all unpaired items
        match self
            .left_iter
            .next()
            .filter(|p| unsafe { p.as_ref().hash.is_some() })
        {
            Some(l) => unsafe {
                let left = &l.as_ref().value;
                let right = self.map_ref.get_right(left).unwrap();
                Some((left, right))
            },
            None => {
                // Ignore all right items that are paired, we've seen those already
                match self
                    .right_iter
                    .next()
                    .filter(|p| unsafe { p.as_ref().hash.is_none() })
                {
                    Some(r) => unsafe {
                        let right = &r.as_ref().value;
                        let left = self.map_ref.get_left(right).unwrap();
                        Some((left, right))
                    },
                    None => None,
                }
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.left_iter.size_hint()
    }
}

impl<L, R, S> FusedIterator for MappedIter<'_, L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
}

/// An iterator over the elements of an inner set of a `PartialCycleMap`.
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

#[cfg(test)]
mod tests {
    use std::hash::Hash;

    use super::PartialCycleMap;

    #[derive(PartialEq, Eq, Hash, Debug)]
    struct TestingStruct {
        pub(crate) value: u64,
        pub(crate) data: String,
    }

    fn construct_default_map() -> PartialCycleMap<String, TestingStruct> {
        (0..100)
            .map(|i| (i.to_string(), TestingStruct::new(i, i.to_string())))
            .collect()
    }

    #[test]
    fn default_construction_test() {
        let map = construct_default_map();
        assert_eq!(map.len(), 100);
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
            let l_pairing = left_opt.unwrap();
            assert_eq!(l_pairing.value, i_str);
            assert_eq!(l_pairing.hash, r_hash);
            let right_opt = map.get_right_inner(&i_struct);
            assert!(right_opt.is_some());
            let r_pairing = right_opt.unwrap();
            assert_eq!(r_pairing.value, i_struct);
            assert_eq!(r_pairing.hash, l_hash);
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
