mod queue;
mod set;

pub use self::queue::Queue;
pub use self::set::Set;

/// The type of a leaf node that holds data
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Container {
    Blob(Vec<u8>),
    Queue(Queue),
    Set(Set),
}
