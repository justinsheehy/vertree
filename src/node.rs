use std::sync::Arc;
use std::cell::RefCell;
use containers::{Container, Blob, Queue, Set};

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum NodeType {
    Directory,
    Blob,
    Queue,
    Set
}

/// A node in a hierarchical version tree
#[derive(Clone, Debug)]
pub struct Node {
    pub path: String,
    pub version: usize,
    pub content: Content
}

impl Node {
    pub fn new<S>(path: S, content: Content) -> Node
        where S: Into<String>
    {
        Node {
            path: path.into(),
            version: 0,
            content: content
        }
    }

    pub fn get_type(&self) -> NodeType {
        match self.content {
            Content::Directory(_) => NodeType::Directory,
            Content::Container(Container::Blob(_)) => NodeType::Blob,
            Content::Container(Container::Queue(_)) => NodeType::Queue,
            Content::Container(Container::Set(_)) => NodeType::Set,
        }
    }
}

/// The contents of a Node
#[derive(Clone, Debug)]
pub enum Content {
    Directory(Vec<Edge>),
    Container(Container)
}

impl Content {
    pub fn new(ty: NodeType) -> Content {
        match ty {
            NodeType::Directory => Content::Directory(vec![]),
            NodeType::Blob => Content::Container(Container::Blob(Blob::new())),
            NodeType::Queue => Content::Container(Container::Queue(Queue::new())),
            NodeType::Set => Content::Container(Container::Set(Set::new()))
        }
    }

    pub fn is_dir(&self) -> bool {
        if let Content::Directory(_) = *self {
            return true;
        }
        false
    }

    /// Return a reference to the blob if the content contains a blob, None otherwise
    pub fn get_blob(&self) -> Option<&Blob> {
        if let Content::Container(Container::Blob(ref blob)) = *self {
            return Some(blob);
        }
        None
    }

    /// Return a reference to the queue if the content contains a queue, None otherwise
    pub fn get_queue(&self) -> Option<&Queue> {
        if let Content::Container(Container::Queue(ref queue)) = *self {
            return Some(queue);
        }
        None
    }

    /// Return a reference to the set if the content contains a set, None otherwise
    pub fn get_set(&self) -> Option<&Set> {
        if let Content::Container(Container::Set(ref set)) = *self {
            return Some(set);
        }
        None
    }

    pub fn get_dir_edges_mut(&mut self) -> Option<&mut Vec<Edge>> {
        if let Content::Directory(ref mut edges) = *self {
            return Some(edges);
        }
        None
    }

    /// Return a mutable reference to the queue if the content contains a queue, None otherwise
    pub fn get_queue_mut(&mut self) -> Option<&mut Queue> {
        if let Content::Container(Container::Queue(ref mut queue)) = *self {
            return Some(queue);
        }
        None
    }

    /// Return a mutable reference to the set if the content contains a set, None otherwise
    pub fn get_set_mut(&mut self) -> Option<&mut Set> {
        if let Content::Container(Container::Set(ref mut set)) = *self {
            return Some(set);
        }
        None
    }
}

/// A single entry in the contents of an interior node
#[derive(Clone, Debug)]
pub struct Edge {
    pub label: String,
    pub node: Arc<RefCell<Node>>
}

impl Edge {
    pub fn new(label: &str, node: Node) -> Edge {
        Edge {
            label: label.to_string(),
            node: Arc::new(RefCell::new(node))
        }
    }
}