use core::borrow::Borrow;
use std::{
    collections::{hash_map::RandomState, HashMap},
    default::Default,
    hash::{BuildHasher, Hash},
};

use hashbrown::{hash_map::DefaultHashBuilder, raw::RawTable};

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
            Some(&right_pair) => {
                let mut digest: Option<&L> = None;
                unsafe {
                    for l_pair in self.left_set.iter_hash(right_pair.hash) {
                        for r_pair in self.right_set.iter_hash(l_pair.as_ref().hash) {
                            if r_pair.as_ref().value == right_pair.value {
                                digest = Some(&l_pair.as_ref().value);
                                break;
                            }
                        }
                    }
                }
                digest
            }
        }
    }

    /// Gets a reference to an item in the right set using an item in the left set.
    pub fn get_right(&self, item: &L) -> Option<&R> {
        match self.get_left_inner(item) {
            None => None,
            Some(&left_pair) => {
                let mut digest: Option<&R> = None;
                unsafe {
                    for r_pair in self.right_set.iter_hash(left_pair.hash) {
                        for l_pair in self.left_set.iter_hash(r_pair.as_ref().hash) {
                            if l_pair.as_ref().value == left_pair.value {
                                digest = Some(&r_pair.as_ref().value);
                                break;
                            }
                        }
                    }
                }
                digest
            }
        }
    }

    #[inline]
    fn get_left_inner(&self, k: &L) -> Option<&MappingPair<L>> {
        let hash = make_hash::<L, S>(&self.hash_builder, k);
        self.left_set.get(hash, equivalent_key(k))
    }

    #[inline]
    fn get_right_inner(&self, k: &R) -> Option<&MappingPair<R>> {
        let hash = make_hash::<R, S>(&self.hash_builder, k);
        self.right_set.get(hash, equivalent_key(k))
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

    pub fn iter_mut(&mut self) -> IterMut<'_, L, R> {
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
