#[macro_use]
extern crate error_chain;

mod errors;
mod container;

use std::sync::Arc;
use std::cell::RefCell;
use errors::*;
use container::{Container, ContainerType};

/// The contents of a Node
#[derive(Clone)]
pub enum Content {
    Directory(Vec<Edge>),
    Leaf(Container)
}

impl Content {
    pub fn new(ty: NodeType) -> Content {
        match ty {
            NodeType::Directory => Content::Directory(vec![]),
            NodeType::Blob => Content::Leaf(Container::new(ContainerType::Blob)),
            NodeType::Queue => Content::Leaf(Container::new(ContainerType::Queue)),
            NodeType::Set => Content::Leaf(Container::new(ContainerType::Set))
        }
    }

    pub fn is_dir(&self) -> bool {
        if let Content::Directory(_) = *self {
            return true;
        }
        false
    }
}

/// A single entry in the contents of an interior node
#[derive(Clone)]
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

#[derive(Copy, Clone, Debug)]
pub enum NodeType {
    Directory,
    Blob,
    Queue,
    Set
}

/// A node in a hierarchical version tree
#[derive(Clone)]
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
}

/// A hierarchical version tree.
///
/// This tree is persistent, and every update to a node both path copies the parent until it gets
/// to the root and increments the parent's version number. Only a single thread can write to the
/// tree at one time.
pub struct Tree {
    root: Arc<RefCell<Node>>
}

impl Tree {
    pub fn new() -> Tree {
        Tree {
            root: Arc::new(RefCell::new(Node::new("/", Content::Directory(vec![]))))
        }
    }

    /// Create a new node of a given type
    ///
    /// This function creates all intermediate directories that don't exist. It returns the
    /// new tree on success. Creation will fail if a directory component of the path matches an
    /// already existing leaf node or the leaf node component of path already exists.
    ///
    /// This function is optimized for the successful case. It walks the tree from the root,
    /// copying on write or creating intermediate directory nodes as required until it gets to the
    /// leaf where it creates and inserts the new leaf node of the proper type. If there is an
    /// error, the new, partially path-copied tree is discarded as the root goes out of scope.
    /// This is an optimization on the successful path because it doesn't require traversing down
    /// the tree and then back upwards. It also doesn't require the use of parent pointers. Finally
    /// it doesn't rely on recursion, since Rust does not have tail recursion and we don't want to
    /// limit the depth of the tree arbitrarily.
    pub fn create<S>(&self, path: S, ty: NodeType) -> Result<Tree>
        where S: Into<String>
    {
        let path = try!(validate_path(path));
        let root = cow_node(&self.root);
        let mut node = root.clone();
        let mut iter = path.split('/').peekable();
        while let Some(s) = iter.next() {
            // This is the last component in the path
            if iter.peek().is_none() {
                println!("insert leaf {}", s);
                try!(insert_leaf(node.clone(), &s, ty));
                break;
            }
            println!("insert dir {}", s);
            node = try!(insert_dir(node.clone(), &s));
        }
        return Ok(Tree {root: root})
    }
}

/// Check for a leading slash and at least one level of depth in path.
///
/// Strip leading and trailing slashes and return normalized path as String
fn validate_path<S>(path: S) -> Result<String>
    where S: Into<String>
{
    let path = path.into();
    if !path.starts_with("/") {
        return Err(ErrorKind::BadPath(format!("{} does not start with a '/'", path)).into())
    }
    let path = path.trim_matches('/').to_string();
    if path.len() == 0 {
        return Err(ErrorKind::BadPath("Path must contain at least one component".to_string())
                   .into());
    }
    Ok(path)
}

fn insert_dir(parent: Arc<RefCell<Node>>, label: &str) -> Result<Arc<RefCell<Node>>>
{
    let mut path = parent.borrow().path.clone();
    path.push_str(label);
    if let Content::Directory(ref mut edges) = parent.borrow_mut().content {
        match edges.binary_search_by_key(&label, |e| &e.label) {
            Ok(index) => {
                // Unsafe because of the call to edges.get_unchecked_mut(index).
                // We know it's safe though because we just got the index in our binary search.
                unsafe {
                    let ref mut child = edges.get_unchecked_mut(index);
                    if !child.node.borrow().content.is_dir() {
                        let ref child_path = child.node.borrow().path;
                        let msg = format!("{} is a leaf node", child_path);
                        return Err(ErrorKind::InvalidPathContent(msg).into());
                    }
                    // Create a copy of child node and replace the old node
                    let node = cow_node(&child.node);
                    child.node = node.clone();
                    return Ok(node);
                }
            },
            Err(index) => {
                let content = Content::new(NodeType::Directory);
                // Edge doesn't exist, let's create it in the proper sort position
                let edge = Edge::new(label, Node::new(path, content));
                let node = edge.node.clone();
                edges.insert(index, edge);
                return Ok(node);
            }
        }
    }
    Err(ErrorKind::InvalidPathContent(parent.borrow().path.clone()).into())
}

fn insert_leaf(parent: Arc<RefCell<Node>>, label: &str, ty: NodeType) -> Result<()> {
    let mut path = parent.borrow().path.clone();
    path.push_str(label);
    if let Content::Directory(ref mut edges) = parent.borrow_mut().content {
        // Assume sorted vec
        if let Err(index) = edges.binary_search_by_key(&label, |e| &e.label) {
            // Edge doesn't exist, let's create it in proper sort position
            let edge = Edge::new(label, Node::new(path, Content::new(ty)));
            edges.insert(index, edge);
            return Ok(());
        }
        return Err(ErrorKind::AlreadyExists(path).into());
    }
    Err(ErrorKind::InvalidPathContent(parent.borrow().path.clone()).into())
}

/// Deep clone a node and bump it's version
fn cow_node(node: &Arc<RefCell<Node>>) -> Arc<RefCell<Node>> {
    // Create a shallow copy of the node (inc ref count on Arc)
    let mut new_node = node.clone();

    // Force a deep copy on write copy and increment the version number
    Arc::make_mut(&mut new_node).borrow_mut().version += 1;
    new_node
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn create_nodes() {
        let tree = Tree::new();
        let tree = tree.create("/somenode", NodeType::Blob).unwrap();
        if let Content::Directory(ref edges) = tree.root.borrow().content {
            assert_eq!(edges.len(), 1);
            assert_eq!(edges[0].label, "somenode".to_string());
        }
        println!("{:?}", tree.root.borrow().path);
    }
}
