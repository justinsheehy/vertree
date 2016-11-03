mod blob;
mod queue;
mod set;

pub use self::blob::{Blob, BlobOp};
pub use self::queue::{Queue, QueueOp};
pub use self::set::{Set, SetOp};

/// The type of a leaf node that holds data
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Container {
    Blob(Blob),
    Queue(Queue),
    Set(Set)
}

/// A Guard on a CAS operation
///
/// A guard is true if the current version of the node at `path` is the same as `version`.
#[derive(Clone, Debug)]
pub struct Guard {
    path: String,
    version: usize
}

/// A representation of a tree-level compare-and-swap operation
///
/// All guards must evaluate to true for the operations to run
#[derive(Clone, Debug)]
pub struct Cas {
    guards: Vec<Guard>,
    ops: Vec<Op>
}

#[derive(Clone, Debug)]
pub enum Op {
    Blob(BlobOp),
    Queue(QueueOp),
    Set(SetOp)
}

impl Op {
    /// Returns true if the operation requires updating the tree
    pub fn is_write(&self) -> bool {
        match *self {
            Op::Blob(ref op) => op.is_write(),
            Op::Queue(ref op) => op.is_write(),
            Op::Set(ref op) => op.is_write()
        }
    }
}

/// Values included in successful replies to Operations
#[derive(Clone, Debug)]
pub enum Value<'a> {
    Blob(&'a Blob),
    OwnedBlob(Blob),
    Set(&'a Set),
    OwnedSet(Set),
    Int(usize),
    Bool(bool),
    None
}

/// The result of running an operation
#[derive(Clone, Debug)]
pub struct Reply<'a> {
    pub path: Option<String>,
    pub version: Option<usize>,
    pub value: Value<'a>
}
