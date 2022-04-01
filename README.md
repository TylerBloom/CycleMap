## About
NOTE: This project is still very much in the works.


DoubleMap provides several map types that can be used to associate
items together while maintaining lookup speeds on par with the
standard [HashMap](https://crates.io/crates/hashbrown).

There are many ways that you might want to map two sets of items,
DoubleMap supports four.
 - There are bijective maps, every item is always paired with exact one
 	 other
 - Partial bijective maps, every item is paired with at most one other
 	 item
 - Injective maps, every item in set A is mapped to an item in set B but
 	 not uniquely, and every element in B has at least one item mapped to
 	 it
 - Partial injective maps, every item in set A is mapped to at most one
 	 item in set B, and items in set B don't have to have an item paired
 	 with it

## How it Works
There is one core algorithm that underlies all of these maps. Each map
contains two HashSets, a left set and a right set. When two items are
paired, they form a cycle. Their hashes are associated with each and can
be used to lookup each other. This means that a cycle can be found
(uniquely) using either item or the pair of their hashes.

This leads to the core invariant of the cycle algorithm: If two items
form a cycle, then the pair of their hashes must be unique.

This invariant is enforced during inserts and swaps (i.e. then items are
added). Should an insert or swap break this invariant, the old pair is
removed and returned and the new pair in put in its place. 

Of note, it is possible that two items with identical hashes in a map so
long as the items they are mapped to don't have the same hash. Also of
note, if you assume that an item's hash is "random", then it is
extremely unlikely for this kind of collision to occur.

