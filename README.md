# vertree

[![Build
Status](https://travis-ci.org/justinsheehy/vertree.svg?branch=master)](https://travis-ci.org/justinsheehy/vertree)

[API Documentation](https://docs.rs/vertree)


This is a library providing the "vertree" data structure. This data structure has the following core properties:

* hierarchical storage (a tree) of data
* rich data structures at the leaves (not just blobs)
* linear versioning of all changes to items and subtrees
* CAS and related operations

The hierarchical structure of vertree is similar to a traditional filesystem. Each inner (non-leaf) node is a "Directory" node, a mapping of UTF-8 strings to child nodes of that Directory. Each leaf node has a specific data type such as Blob, Queue, or Set, with corresponding operations available to modify the data in the node. The sub-items inside Queue and Set nodes are always Blob, so a leaf node itself is not arbitrarily complex in content.

One of the essential features of vertree is that every node has a version. All mutation operations on either a leaf node's content (such as pushing something into a Queue) or on the vertree itself (such as creating or deleting a node) cause the version to be incremented both at the node where the change occurred and at every node above it. This allows a special capability: operations in vertree can be conditional on either individual nodes or arbitrary subtrees, enabling easy optimistic concurrency among users that the vertree's content is exposed to.

