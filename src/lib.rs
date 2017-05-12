//! Vertree provides a persistent trie for storing versioned, hierarchical, typed data.
//!
//! By Hierarchical, we mean that the code uses a filesystem like tree structure. In contrast to a
//! normal trie, the key in each node is not a single character but a subset of a path between
//! slashes. This allows us to ignore language encoding while still storing all keys in UTF-8 and
//! providing lexicographically sorted keys.
//!
//! Each inner node in the tree is a directory which contains an array of pointers to it's child
//! nodes. Each leaf node is of a specific datastructure type. Leafs can be of type set, queue, or
//! blob. A blob stores an array of bytes. Sets and queues store blobs.
//!
//! A vertree is persistent, in the functional programming sense of the term, meaning, it is
//! copy-on-write. Each update of a vertree results in a new vertree that shares structure with
//! unchanged nodes in the previous vertree. Furthermore, when updating a node in the tree, all the
//! nodes that are path copied from the updated node to the root have their versions bumped. This
//! allows performing CAS operations on entire subtrees.
//!
//! The persistent functionality is provided via the use of Atomic Refcounted (Arc) pointers.
//! Garbage collection is performed when the refcount of nodes reaches 0. Note that this does not
//! require epoch reclamation as used in [crossbeam](https://github.com/aturon/crossbeam), because
//! all updates are performed on a single thread. This use of `Arc` instead of `Rc` pointers for
//! nodes allows immutable trees to be shared among threads. Note that updates on different threads
//! will create new diverging trees, rather than a single 'latest tree'. For that we would require
//! crossbeam.

// Used by containers/Set
// See https://github.com/rust-lang/rust/issues/34511
#![feature(conservative_impl_trait)]

#[cfg(test)]
#[macro_use]
extern crate quickcheck;

extern crate rmp as msgpack;

#[cfg(test)]
extern crate rand;

#[macro_use]
extern crate error_chain;

#[cfg(test)]
#[macro_use]
extern crate assert_matches;

#[cfg(test)]
mod arbitrary;

mod errors;
mod snapshot;
mod tree;
mod node;
mod cas;
pub mod iterators;
pub mod containers;

pub use errors::*;
pub use tree::{Tree, Reply, Value};
pub use node::NodeType;
pub use cas::{WriteOp, Guard};
