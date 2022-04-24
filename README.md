[![Crates.io](https://img.shields.io/crates/v/cycle_map.svg)](https://crates.io/crates/cycle_map)
[![Documentation](https://docs.rs/cycle_map/badge.svg)](https://docs.rs/cycle_map/)
![GitHub Workflows](https://github.com/TylerBloom/CycleMap/actions/workflows/ci.yml/badge.svg)
[![Coverage Status](https://codecov.io/gh/TylerBloom/CycleMap/branch/main/graph/badge.svg)](https://codecov.io/gh/TylerBloom/CycleMap)
![Maintenance](https://img.shields.io/badge/Maintenance-Actively%20Developed-brightgreen.svg)

## About
CycleMap provides several "double-sided" hash maps that associate items
between two sets. It does this without keep duplicate data and while
maintaining lookup speeds on par with the standard
[HashMap](https://crates.io/crates/hashbrown).

There are many ways that you might want to map items between sets.
CycleMap supports three.
 - Bijective maps: every item in both sets is paired, and paired with
 	 exactly one other item
 - Partial bijective maps: items in either set don't have to be paired,
 	 but any paired item is paired with exactly one other item
 - (Weakly) Surjective maps: every item in the left set is paired with
 	 exactly one right item, and items in the right set can be paired with
 	 multiple (or no) items from the left set

## How it Works
Each map contains two sets, a left set and a right set. When two items
are paired, they form a cycle. That is, an item from either set can be
used to uniquely lookup the item(s) it is paired with. This forms a
cyclic lookup and is the core algorithm that underlies all cycle maps. 

Instead of holding self-referential pointers, all cycle maps pair an
item with the hash of its partner item (and an id). This prevents
possible unforeseen memory bugs and makes map resizing faster since an
item doesn't need to "know" *where* its partner is but rather *how* to
get there.

## Why use 
Cycle maps aren't meant to replace the standard hashmap. In fact, they
are built on top of it. Rather, they provide a clean solution to fast,
bi-direction lookups.

If you find yourself creating workarounds to these sorts of problems,
give a cycle map a try.

## Contribution
If you want to contribute to or improve upon this library, please do so.
Fork this project or submit an issue or a pull request for a
feature/fix/change/etc. All that I ask is for derived/iterative
libraries to be open and free to use and ideally with the same license
(LGPL v3). Any other application or library that uses this library can
use any license.

## Future Plans
The `CycleMap` struct has a counterpart, `PartialCycleMap`. This struct
looses the requirements of the `CycleMap` by allowing unpaired items in
either set. A similar `PartialGroupMap` struct is planned to mirror the
`GroupMap` struct.
