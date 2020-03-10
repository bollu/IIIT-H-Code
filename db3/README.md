# 20161105

Use a struct to have `vals`, `children`, and `routers` pointers.
Implementation mostly followed from link:

> // https://www.cs.helsinki.fi/u/mluukkai/tirak2010/B-tree.pdf

#### `insert`

walk the tree top-down, splitting a node if it is full so that
we have enough space for leaf nodes to be addded.

On reaching a leaf node, if full, use parent pointer to split
leaf node and add split leaf node into parent pointer. We know
parent has space since we split the parent as we walk
down the tree. 

Once we have enough space, insert the node.

#### `range(x, y)`:

Implement just like `find`, except instead of walking down just
one branch of the tree, walk down all nodes between the routers
which mark out the section `(x..y)`. Recursively call `range`
on all the nodes that our routers tell us to walk down on,
and then add the values up.

#### `count(x)`:

`count(x)` is equivalent to `range(x, y)`.

#### `find(x)`:

`find(val)` is equivalent to `count(val) >= 1`. So implement
find as a call to `count(val) >= 1`.



