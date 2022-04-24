//! This crate contains several bi-directional map types that help pair items between two sets.
//! Unlike a traditional hashmap, every item in any cycle map can be used as a key to access its
//! companion item(s). They do this while keeping a single copy of each item and while maintaining
//! lookup speeds on par with those of a standard hash map. This crate is build on top of the
//! [`hashbrown`] implementation of a hash table to provide effiecent storage and lookups.
//!
//! Items are stored with the hashes of either companion item. This hash, along with an id, is used
//! to uniquely lookup items between sets. That is, given some item in the left set, its companion
//! item can always be found and used to find the given left item (and visa versa).
//!
//! This crate contains three different maps. There are two kinds of maps for mapping pairs of items
//! (i.e. one-to-one). One map, [`CycleMap`], forces every item to be paired. The other,
//! [`PartialCycleMap`] allows for items to be unpaired. The last map, [`GroupMap`],
//! allow multiple (left) item to be paired with one right item.
//!
//! CycleMap is build on top of [`hashbrown`]. All maps use its default hashing algorithm, but
//! different hashing algorithms can be specified on creation of any map.

#![deny(unused_imports, missing_debug_implementations, unreachable_pub)]
#![cfg_attr(doc, deny(missing_docs, rustdoc::broken_intra_doc_links))]
#![warn(rust_2018_idioms)]

/// A strict one-to-one map
pub mod cycle_map;
/// A strict one-to-one map
pub use crate::cycle_map::CycleMap;

/// A weak one-to-one map
pub mod partial_cycle_map;
/// A weak one-to-one map
pub use crate::partial_cycle_map::PartialCycleMap;

/// A strick many-to-one map
pub mod group_map;
/// A strick many-to-one map
pub use crate::group_map::GroupMap;

/// Enums similar to Option
pub mod optionals;
pub use crate::optionals::*;

/// Various helpful functions
pub(crate) mod utils;
