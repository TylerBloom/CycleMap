use std::{
    fmt,
    hash::{BuildHasher, Hash},
};

use hashbrown::raw::RawTable;

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

pub(crate) fn does_map<'a, P, Q>(
    value: &'a P,
    map_ref: &'a RawTable<MappingPair<P>>,
) -> impl Fn(&MappingPair<Q>) -> bool + 'a
where
    P: Hash + PartialEq + Eq,
    Q: Hash + PartialEq + Eq + ?Sized,
{
    move |pair| map_ref.get(pair.hash, equivalent_key(value)).is_some()
}

pub(crate) fn make_hash<T, S>(hash_builder: &S, val: &T) -> u64
where
    T: Hash + ?Sized,
    S: BuildHasher,
{
    use core::hash::Hasher;
    let mut state = hash_builder.build_hasher();
    val.hash(&mut state);
    state.finish()
}

pub(crate) fn make_hasher<T, S>(hash_builder: &S) -> impl Fn(&T) -> u64 + '_
where
    T: Hash,
    S: BuildHasher,
{
    move |val| make_hash::<T, S>(hash_builder, val)
}

// Contains a value and the hash of the item that the value maps to.
pub(crate) struct MappingPair<T> {
    pub(crate) value: T,
    pub(crate) hash: u64,
    pub(crate) id: u64,
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
            hash: self.hash.clone(),
            id: self.id.clone(),
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
