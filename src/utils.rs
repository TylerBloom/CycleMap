use std::hash::{BuildHasher, Hash};

/// Creates a hash
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

/// Creates a hasher
pub(crate) fn make_hasher<T, S>(hash_builder: &S) -> impl Fn(&T) -> u64 + '_
where
    T: Hash,
    S: BuildHasher,
{
    move |val| make_hash::<T, S>(hash_builder, val)
}
