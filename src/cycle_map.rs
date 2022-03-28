use core::borrow::Borrow;
use std::{
    collections::{hash_map::RandomState, HashMap},
    default::Default,
    fmt,
    fmt::Debug,
    hash::{BuildHasher, Hash},
    iter::FusedIterator,
    marker::PhantomData,
};

use hashbrown::{
    hash_map::DefaultHashBuilder,
    raw::{RawDrain, RawIntoIter, RawIter, RawTable},
};

use crate::optional_pair::OptionalPair;

fn equivalent_key<Q: PartialEq + ?Sized>(k: &Q) -> impl Fn(&MappingPair<Q>) -> bool + '_ {
    move |x| k.eq(&x.value)
}

pub(crate) fn make_hash<K, S>(hash_builder: &S, val: &K) -> u64
where
    K: Hash + ?Sized,
    S: BuildHasher,
{
    use core::hash::Hasher;
    let mut state = hash_builder.build_hasher();
    val.hash(&mut state);
    state.finish()
}

// Contains a value and the hash of the item that the value maps to.
struct MappingPair<T> {
    pub(crate) value: T,
    pub(crate) hash: u64,
}

impl<T> MappingPair<T> {
    // Consumes the pair and returns the held `T`
    pub fn extract(self) -> T {
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
        self.value.eq(&other.value)
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
            hash: self.hash.clone(),
        }
    }
}

impl<T: Debug> fmt::Debug for MappingPair<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "MappingPair {{ value: {:?}, hash: {} }}",
            self.value, self.hash
        )
    }
}

/// A hash map that supports bidirection searches.
///
/// [`CycleMap`] bijectively maps two sets of elements, i.e. every element always
/// has a "companion". It does this while maintaining the same complexitity for "gets"
/// as a traditional [`HashMap`] and while only keeping a single copy of each element.
///
/// It is implemented using two [`HashSet`]s, a "left" and "right" set. On insert, the given pair
/// of items is split. The left item is stored in the left set with the hash of the right item,
/// likewise for the right item. As such, both the left and right types need to implement [`Eq`]
/// and [`Hash`], and as with other hashed collections, it is a logic error for an item to be
/// modified in such a way that the item's hash or its equality, as changes while it is in the bag.
///
/// Sorting values like this allows for look up on pair with a standard HashMap and makes resizes
/// faster but is not with a cost. When inserting a new pair of elements, there is potentail for
/// collision. This collision should be excendingly rare and can only happen upon inserting new
/// elements. You can read more about what causes collisions [here]("").
pub struct CycleMap<L, R, St = DefaultHashBuilder> {
    pub(crate) hash_builder: St,
    left_set: RawTable<MappingPair<L>>,
    right_set: RawTable<MappingPair<R>>,
}

impl<K, V> CycleMap<K, V, DefaultHashBuilder> {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    #[inline]
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
    /// Should the left element be equal to another left element, the old pair is removed and
    /// returned. The same goes for the right element.
    ///
    /// There is a chance for collision here. Collision occurs when the map contains elements with
    /// identical hashes as the given left and right elements, and they are mapped to each other.
    /// In such a case, the old pair is returned and the new pair is inserted.
    pub fn insert(&mut self, left: L, right: R) -> OptionalPair<L, R> {
        todo!()
    }

    /// Gets a reference to an item in the left set using an item in the right set.
    pub fn get_left(&self, item: &R) -> Option<&L> {
        match self.get_right_inner(item) {
            None => None,
            Some(&right_pair) => unsafe {
                let mut digest: Option<&L> = None;
                for l_pair in self.left_set.iter_hash(right_pair.hash) {
                    for r_pair in self.right_set.iter_hash(l_pair.as_ref().hash) {
                        if r_pair.as_ref().value == right_pair.value {
                            digest = Some(&l_pair.as_ref().value);
                            break;
                        }
                    }
                }
                digest
            },
        }
    }

    /// Gets a reference to an item in the right set using an item in the left set.
    pub fn get_right(&self, item: &L) -> Option<&R> {
        match self.get_left_inner(item) {
            None => None,
            Some(&left_pair) => unsafe {
                let mut digest: Option<&R> = None;
                for r_pair in self.right_set.iter_hash(left_pair.hash) {
                    for l_pair in self.left_set.iter_hash(r_pair.as_ref().hash) {
                        if l_pair.as_ref().value == left_pair.value {
                            digest = Some(&r_pair.as_ref().value);
                            break;
                        }
                    }
                }
                digest
            },
        }
    }

    #[inline]
    fn get_left_inner(&self, item: &L) -> Option<&MappingPair<L>> {
        let hash = make_hash::<L, S>(&self.hash_builder, item);
        self.left_set.get(hash, equivalent_key(item))
    }

    #[inline]
    fn get_right_inner(&self, item: &R) -> Option<&MappingPair<R>> {
        let hash = make_hash::<R, S>(&self.hash_builder, item);
        self.right_set.get(hash, equivalent_key(item))
    }
    
    /// Takes an item from the left set and returns it (if it exists).
    /// 
    /// This method is unsafe since removing the item break a cycle in the map.
    /// Ensure that any element you remove this way has its corresponding item removed too.
    pub(crate) unsafe fn remove_left(&mut self, item: &R) -> Option<MappingPair<L>> {
        todo!()
    }
    
    /// Takes an item from the right set and returns it (if it exists).
    /// 
    /// This method is unsafe since removing the item break a cycle in the map.
    /// Ensure that any element you remove this way has its corresponding item removed too.
    pub(crate) unsafe fn remove_right(&mut self, item: &L) -> Option<MappingPair<R>> {
        todo!()
    }
}

impl<L, R, S> Default for CycleMap<L, R, S>
where
    S: Default,
{
    /// Creates an empty `HashMap<K, V, S>`, with the `Default` value for the hasher.
    #[cfg_attr(feature = "inline-more", inline)]
    fn default() -> Self {
        Self::with_hasher(Default::default())
    }
}

impl<L, R, S> CycleMap<L, R, S> {
    pub const fn with_hasher(hash_builder: S) -> Self {
        Self {
            hash_builder,
            left_set: RawTable::new(),
            right_set: RawTable::new(),
        }
    }

    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self {
        Self {
            hash_builder,
            left_set: RawTable::new(),
            right_set: RawTable::new(),
        }
    }

    pub fn hasher(&self) -> &S {
        &self.hash_builder
    }

    pub fn capacity(&self) -> usize {
        // The size of the sets is always equal
        self.left_set.capacity()
    }

    pub fn iter(&self) -> Iter<'_, L, R> {
        // iter should iterator over the pairs (L,R)
        todo!()
    }

    fn raw_capacity(&self) -> usize {
        // The size of the sets is always equal
        self.left_set.buckets()
    }

    pub fn len(&self) -> usize {
        // The size of the sets is always equal
        self.left_set.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn drain(&mut self) -> Drain<'_, L, R> {
        todo!()
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&L, &R) -> bool,
    {
        todo!()
    }

    pub fn drain_filter<F>(&mut self, f: F) -> DrainFilter<'_, L, R, F>
    where
        F: FnMut(&L, &R) -> bool,
    {
        todo!()
    }

    pub fn clear(&mut self) {
        self.left_set.clear();
        self.right_set.clear();
    }
}

/// An iterator over the entry pairs of a `CycleMap`.
pub struct Iter<'a, L, R> {
    left_iter: RawIter<MappingPair<L>>,
    map_ref: &'a CycleMap<L, R>,
}

impl<K, V> Clone for Iter<'_, K, V> {
    fn clone(&self) -> Self {
        Self {
            left_iter: self.left_iter.clone(),
            map_ref: self.map_ref,
        }
    }
}

impl<L: Debug, R: Debug> fmt::Debug for Iter<'_, L, R>
where
    L: Hash + Eq + Debug,
    R: Hash + Eq + Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<'a, L, R> Iterator for Iter<'a, L, R>
where
    L: Hash + Eq,
    R: Hash + Eq,
{
    type Item = (&'a L, &'a R);

    fn next(&mut self) -> Option<(&'a L, &'a R)> {
        match self.left_iter.next() {
            Some(l) => unsafe {
                let left = l.as_ref().value;
                let right = self.map_ref.get_right(&left).unwrap();
                Some((&left, &right))
            },
            None => None,
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.left_iter.size_hint()
    }
}

impl<L, R> ExactSizeIterator for Iter<'_, L, R>
where
    L: Hash + Eq,
    R: Hash + Eq,
{
    fn len(&self) -> usize {
        self.left_iter.len()
    }
}

impl<L, R> FusedIterator for Iter<'_, L, R>
where
    L: Hash + Eq,
    R: Hash + Eq,
{
}

/// An iterator over the entry pairs of a `CycleMap`.
pub struct Drain<'a, L, R> {
    left_iter: RawDrain<'a, MappingPair<L>>,
    map_ref: &'a CycleMap<L, R>,
}


impl<L, R> Drain<'_, L, R> {
    /// Returns a iterator of references over the remaining items.
    pub(super) fn iter(&self) -> Iter<'_, L, R> {
        Iter {
            left_iter: self.left_iter.iter(),
            map_ref: self.map_ref
        }
    }
}

impl<'a, L, R> Iterator for Drain<'a, L, R> {
    type Item = (L, R);

    fn next(&mut self) -> Option<(L, R)> {
        match self.left_iter.next() {
            Some(l) => unsafe {
                let left = l.extract();
                let right = self.map_ref.get_right(&left).unwrap();
                Some((&left, &right))
            },
            None => None,
        }
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.left_iter.size_hint()
    }
}
impl<K, V> ExactSizeIterator for Drain<'_, L, R> {
    fn len(&self) -> usize {
        self.left_iter.len()
    }
}
impl<L, R> FusedIterator for Drain<'_, L, R> {}

impl<L, R> fmt::Debug for Drain<'_, L, R>
where
    L: fmt::Debug,
    R: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}
