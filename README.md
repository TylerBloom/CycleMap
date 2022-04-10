[![Crates.io](https://img.shields.io/crates/v/cycle_map.svg)](https://crates.io/crates/cycle_map)
[![Documentation](https://docs.rs/cycle_map/badge.svg)](https://docs.rs/cycle_map/)
![GitHub Workflows](https://github.com/TylerBloom/CycleMap/actions/workflows/ci.yml/badge.svg)
[![Coverage Status](https://codecov.io/gh/TylerBloom/CycleMap/branch/main/graph/badge.svg)](https://codecov.io/gh/TylerBloom/CycleMap)
![Maintenance](https://img.shields.io/badge/Maintenance-Actively%20Developed-brightgreen.svg)

## About
NOTE: This project is still very much in the works. If you'd like to see
a more detailed status of this repo, see the "Progress" section at the
end of this Readme.


CycleMap provides several "double-sided" hash maps that associate items
between two sets. It does this without keep duplicate data and while
maintaining lookup speeds on par with the standard
[HashMap](https://crates.io/crates/hashbrown).

There are many ways that you might want to map items between sets.
CycleMap supports four.
 - Bijective maps: every item in both sets is paired, and paired with
 	 exactly one other item
 - Partial bijective maps: items in either set don't have to be paired,
 	 but any paired item is paired with exactly one other item
 - Injective maps: every item in both sets is paired, but items in the
 	 right set can be paired with multiple items from the left set
 - Partial injective maps: items in either set don't have to be paired,
 	 but items in the right set can be paired with multiple items from the
 	 left set

## How it Works
Each map contains two sets, a left set and a right set. When two items
are paired, they form a cycle. That is, given an item from either set,
it can be used to unique lookup the item(s) it is paired with. This is
the core algorithm that underlies all cycle maps. 

Instead of holding self-referential pointers, all cycle maps pair an
item with the hash of its partner item (and an id). This prevents
possible unforeseen memory bugs and makes map resizing faster since an
item doesn't need to "know" *where* its partner is but rather *how* to
get there.

## Why use 
Cycle maps aren't meant to replace the standard hashmap (which they are
build on). Rather, they provide a clean solution to fast bidirection
data lookups.

If you find yourself creating workarounds to these sorts of problems,
give a cycle map a try.

## Contribution
If you want to contribute to or improve upon this library, please do so.
Fork this project or submit an issue or a pull request for a
feature/fix/change/etc. All that I ask is for derived/iterative
libraries to be open and free to use and ideally with the same license
(LGPL v3). Any other application or library that uses this library can
use any license.

## Progress
CycleMap will be published to `crate.io` once all the aforementioned
maps are completed and mostly stabalized. Until then, I will consider
the library to be `pre-0.1` and with generally unstable APIs. Parts of
the library up until then will be in a usable state. If you want to use
them before `v0.1`, I **highly** suggest that you track which commit you
are using to avoid commit-to-commit breaking changes.

Below are the current states of all the map:
	- [x] `CycleMap`: This is the standard bijective map. It is mostly
		ready for public use, but work on the remaining maps might cause
		some changes.
	- [x] `PartialCycleMap`: This is the partially bijective map. It too is
		mostly ready for public use, but work on the remaining maps might
		cause some changes.
	- [ ] `MultiCycleMap`: This is the injective map. Work on this map has
		yet to start.
	- [ ] `PartialMultiCycleMap`: This is the partially injective map.
		Work on this map has yet to start.
	- [ ] `Optionals`: For egonomics, the cycle maps uses their own
		variant of the rust `Option`. Currently, this is just the
		`OptionalPair`, but will like expand will its functionalities.

