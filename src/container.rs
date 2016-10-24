use std::collections::{VecDeque, HashSet};

pub enum ContainerType {
    Blob,
    Queue,
    Set
}

/// The type of a leaf node that holds data
#[derive(Clone)]
pub enum Container {
    Blob(Vec<u8>),
    Queue(VecDeque<Vec<u8>>),
    Set(HashSet<Vec<u8>>)
}

impl Container {
    pub fn new(ty: ContainerType) -> Container {
        match ty {
            ContainerType::Blob => Container::Blob(vec![]),
            ContainerType::Queue => Container::Queue(VecDeque::new()),
            ContainerType::Set => Container::Set(HashSet::new())
        }
    }
}
