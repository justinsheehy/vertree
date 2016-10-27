mod blob;
mod queue;
mod set;

pub use self::blob::{Blob, BlobOp};
pub use self::queue::{Queue, QueueOp};
pub use self::set::{Set, SetOp};

/// The type of a leaf node that holds data
#[derive(Clone, Debug)]
pub enum Container {
    Blob(Blob),
    Queue(Queue),
    Set(Set)
}

/// A Guard on a CAS operation
///
/// A guard is true if the current version of the node at `path` is the same as `version`.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Guard {
    path: String,
    version: usize
}

/// A representation of a tree-level compare-and-swap operation
///
/// All guards must evaluate to true for the operations to run
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Cas {
    guards: Vec<Guard>,
    ops: Vec<Op>
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum Op {
    Blob(BlobOp),
    Queue(QueueOp),
    Set(SetOp)
}

