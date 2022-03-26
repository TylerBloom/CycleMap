use std::{
    collections::{hash_map::RandomState, HashMap, HashSet},
    default::Default,
    hash::{BuildHasher, Hash},
};

use crate::optional_pair::OptionalPair;

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
pub struct CycleMap<L, R, St = RandomState> {
    left_set: HashSet<(L, u64), St>,
    right_set: HashSet<(R, u64), St>,
}

impl<L, R> CycleMap<L, R, RandomState>
where
    L: Eq + Hash,
    R: Eq + Hash,
{
    pub fn new() -> Self {
        todo!()
    }
    
    pub fn with_capacity() -> Self {
        todo!()
    }
    
    /// Adds a pair of items to the map.
    /// 
    /// Should the left element be equal to another left element, the old pair is removed and
    /// returned. The same goes for the right element.
    ///
    /// There is a chance for collision here. Collision occurs when the map contains elements with
    /// identical hashes as the given left and right elements, and they are mapped to each other.
    /// In such a case, the old pair is returned and the new pair is inserted.
    pub fn insert(&mut self, left: L, right: R) -> OptionalPair<L,R> {
        todo!()
    }
    
    pub fn get_left() -> () {
        todo!()
    }
    
    pub fn get_right() -> () {
        todo!()
    }
}
