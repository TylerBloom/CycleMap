//! This is a crate that does things

#![deny(
    dead_code,
    unused_imports,
    missing_debug_implementations,
    unreachable_pub
)]
#![cfg_attr(doc, deny(missing_docs, rustdoc::broken_intra_doc_links))]
#![warn(rust_2018_idioms)]

/// One of the main data structs
pub mod cycle_map;

/// Enums similar to Option used with pairs of items
pub mod optionals;

/// Various helpful functions
pub(crate) mod utils;
