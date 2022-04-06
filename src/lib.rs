//! This is a crate that does things

#![deny(unused_imports, missing_debug_implementations, unreachable_pub)]
#![cfg_attr(doc, deny(missing_docs, rustdoc::broken_intra_doc_links))]
#![warn(rust_2018_idioms)]

/// One of the main data structs
pub mod cycle_map;
pub use crate::cycle_map::*;

/// One of the main data structs
pub mod partial_cycle_map;
pub use crate::partial_cycle_map::*;

/// Enums similar to Option used with pairs of items
pub mod optionals;
pub use crate::optionals::*;

/// Various helpful functions
pub(crate) mod utils;
