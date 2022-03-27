## About
NOTE: This project is still very much in the works.


DoubleMap provides several map types that can be used to associate
elements together while maintaining lookup speeds on par with the
standard HashMap.

There are many ways that you might want to map two sets of items,
DoubleMap supports three.
There are bijective maps (every item is always paired with exact one
other), partial bijective maps (every item is paired with at most one
other item), and injective maps (every item in set A is mapped to
an item in set B but not uniquely).

# How it Works
There is one core algorithm that underlies all of these maps.
Each map contains two HashSets, a left set and a right set.
When a pair of items is inserted into the map, the left item is paired
with the hash of the right item and stored in the left set.
The same goes for the right item.
When you want to get an item in the right set via the left set, the hash
that's paired with the left item is used to lookup the right item.

Of note, it is possible that two items with identical hashes are
inserted into the map.
This is generally not an issue.


