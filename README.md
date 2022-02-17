## About
DoubleMap is a is a collection that helps map data using two keys, a
primary (required) key and a secondary (optional) key. This project is
still very much in the works.

Goals of this data structure:
<ul>
<li>Allow for values to be mapped by two keys</li>
<li>Secandary keys can be deleted without affecting the backing data</li>
<li>Deleting a primary key removes the backing value and the associated secondary key (if one exists)</li>
<li>Minimize data duplication</li>
<ul>
				<li>Different amounts of duplication will be needed based on the constraints of the map</li>
</ul>
</ul>
