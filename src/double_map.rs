use std::{
    collections::{hash_map::RandomState, HashMap},
    default::Default,
    hash::{BuildHasher, Hash},
};

pub struct DoubleMap<P, S, V, St = RandomState> {
    primary_map: HashMap<P, V, St>,
    secondary_map: HashMap<S, P, St>,
}

// Known issue: There isn't a one-to-one mapping between secondary keys and primary keys.
// That is, two secondary keys, say a & b, could both map to some primary key, p.
// This feels like a problem... 
impl<P, S, V, St> DoubleMap<P, S, V, St>
where
    P: Hash + Eq,
    S: Hash + Eq,
    St: Default + BuildHasher,
{
    #[inline]
    pub fn new() -> DoubleMap<P, S, V, St> {
        Default::default()
    }

    #[inline]
    pub fn insert_primary(&mut self, primary: P, value: V) -> Option<V> {
        self.primary_map.insert(primary, value)
    }

    #[inline]
    pub fn insert_secondary(&mut self, secondary: S, primary: P) -> Option<P> {
        self.secondary_map.insert(secondary, primary)
    }
    
    #[inline]
    pub fn get(&self, primary: &P) -> Option<&V> {
        self.primary_map.get(primary)
    }
    
    #[inline]
    pub fn get_mut(&mut self, primary: &P) -> Option<&mut V> {
        self.primary_map.get_mut(primary)
    }
    
    #[inline]
    pub fn get_primary(&self, secondary: &S) -> Option<&P> {
        self.secondary_map.get(secondary)
    }
    
    #[inline]
    pub fn get_with_secondary(&self, secondary: &S) -> Option<&V> {
        let key: &P = self.get_primary(secondary)?;
        self.primary_map.get(key)
    }
    
    #[inline]
    pub fn get_mut_with_secondary(&mut self, secondary: &S) -> Option<&mut V> {
        let key: &P = self.secondary_map.get(secondary)?;
        self.primary_map.get_mut(key)
    }
}

impl<P, S, V, St> Default for DoubleMap<P, S, V, St>
where
    St: Default,
{
    #[inline]
    fn default() -> DoubleMap<P, S, V, St> {
        DoubleMap {
            primary_map: HashMap::with_hasher(Default::default()),
            secondary_map: HashMap::with_hasher(Default::default()),
        }
    }
}
