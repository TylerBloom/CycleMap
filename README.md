## About
DoubleMap is a is a collection that helps map data using two keys, a
primary (required) key and a secondary (optional) key. This project is
still very much in the works.

Goals of this data structure:
<ul>
<li>Allow for values to be mapped by two keys</li>
<li>Secandary keys can be deleted without affecting the backing data</li>
<li>Deleting a primary key removes the backing value and the associated secondary key (if one exists)</li>
<li>Accessing and deleting data from the map (regardless of key type) should have the same complexity as the `std` map.</li>
<ul>
	<li>In particular, removing a primary key removes the associated secondary key (if one exists), so lookups between primary and secondary keys need to be bidirectional (well, technically only injective from secondary to primary).</li>
</ul>
<li>Minimize data duplication</li>
<ul>
	<li>Different amounts of duplication will be needed based on the constraints of the map</li>
</ul>
</ul>
