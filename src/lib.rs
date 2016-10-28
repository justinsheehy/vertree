#![feature(proc_macro)]

#[macro_use]
extern crate error_chain;

#[macro_use]
extern crate serde_derive;

#[cfg(test)]
#[macro_use]
extern crate assert_matches;

mod errors;
pub mod containers;

use std::sync::Arc;
use std::cell::RefCell;
use errors::*;
use containers::{Container, Blob, BlobOp, Queue, QueueOp, Set, SetOp, Value, Reply, Op};

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
}

/// A single entry in the contents of an interior node
#[derive(Clone, Debug)]
pub struct Edge {
    label: String,
    node: Arc<RefCell<Node>>
}

impl Edge {
    pub fn new(label: &str, node: Node) -> Edge {
        Edge {
            label: label.to_string(),
            node: Arc::new(RefCell::new(node))
        }
    }
}

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
    path: String,
    version: usize,
    content: Content
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

/// A hierarchical version tree.
///
/// This tree is persistent, and every update to a node both path copies the parent until it gets
/// to the root and increments the parent's version number. Only a single thread can write to the
/// tree at one time.
#[derive(Debug, Clone)]
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
            if iter.peek().is_none() {
                // This is the last component in the path
                try!(insert_leaf(node.clone(), &s, ty));
                break;
            }
            node = try!(insert_dir(node.clone(), &s));
        }
        return Ok(Tree {root: root})
    }

    pub fn iter(&self) -> Iter {
        Iter {
            stack: vec![&self.root]
        }
    }

    pub fn run(&self, op: Op) -> Result<(Reply, Option<Tree>)> {
        if op.is_write() {
            return self.update(op);
        }
        let replies = try!(self.read(op));
        Ok((replies, None))
    }

    fn update(&self, op: Op) -> Result<(Reply, Option<Tree>)> {
        // TODO: complete this
        unreachable!()
    }

    fn read(&self, op: Op) -> Result<Reply> {
        match op {
            Op::Blob(op) => self.read_blob(op),
            _ => unreachable!()
//            Op:Queue(op) => read_queue(&self, op),
//            Op:Set(op) => read_set(&self, op)
        }
    }

    fn read_blob(&self, op: BlobOp) -> Result<Reply> {
        let reply = match op {
            BlobOp::Get {path} => {
                let (blob, version) = try!(self.find_blob(&path));
                Reply {
                    path: path,
                    version: version,
                    value: Value::Blob(blob)
                }
            },
            BlobOp::Len {path} => {
                let (blob, version) = try!(self.find_blob(&path));
                Reply  {
                    path: path,
                    version: version,
                    value: Value::Int(blob.len())
                }
            },
            _ => unreachable!()
        };
        Ok(reply)
    }

    fn find_blob(&self, path: &str) -> Result<(&Blob, usize)> {
        let (content, version) = try!(self.find(path, NodeType::Blob));
        if let Content::Container(Container::Blob(ref blob)) = *content {
            return Ok((blob, version));
        }
        unreachable!();
    }

    fn find(&self, path: &str, ty: NodeType) -> Result<(&Content, usize)> {
        let mut parent = &self.root;
        let mut iter = path.split('/').peekable();
        while let Some(s) = iter.next() {
            unsafe {
                if let Content::Directory(ref edges) = (*parent.as_ptr()).content {
                    if let Ok(index) = edges.binary_search_by_key(&s, |e| &e.label) {
                        if iter.peek().is_none() {
                            let node = &(*edges.get_unchecked(index).node.as_ptr());
                            let node_ty = node.get_type();
                            if node_ty != ty {
                                return Err(ErrorKind::WrongType(node.path.clone(), node_ty).into());
                            }
                            return Ok((&node.content, node.version))
                        }
                        parent = &edges.get_unchecked(index).node;
                        continue;
                    }
                }
                return Err(ErrorKind::DoesNotExist(parent.borrow().path.clone()).into());
            }
        }
        unreachable!();
    }
}

/// Directories contain a list of labels for each edge
/// Containers are an actual reference to the Container and it's data
pub enum IterContent<'a> {
    Directory(Vec<&'a str>),
    Container(&'a Container)
}

pub struct IterNode<'a> {
    pub path: &'a str,
    pub version: usize,
    pub content: IterContent<'a>
}

/// An iterator that performs a depth first walk of the entire tree.
pub struct Iter<'a> {
    stack: Vec<&'a Arc<RefCell<Node>>>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = IterNode<'a>;
    fn next(&mut self) -> Option<IterNode<'a>> {
        if self.stack.len() == 0 {
            return None;
        }
        let node = self.stack.pop().unwrap();
        unsafe {
            let ptr = node.as_ptr();
            let content = match (*ptr).content {
                Content::Directory(ref edges) => {
                    self.stack.extend(edges.iter().rev().map(|edge| &edge.node));
                    IterContent::Directory(edges.iter().map(|edge| &edge.label as &str).collect())
                },
                Content::Container(ref container) => {
                    IterContent::Container(&container)
                }
            };
            Some(IterNode {
                path: &(*ptr).path,
                version: (*ptr).version,
                content: content
            })
        }
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
    if path.len() != 1 {
        // We aren't at the root.
        path.push_str("/");
    }
    path.push_str(label);
    let mut parent = parent.borrow_mut();
    if let Content::Directory(ref mut edges) = parent.content {
        match edges.binary_search_by_key(&label, |e| &e.label) {
            Ok(index) => {
                // Unsafe block needed because of the call to edges.get_unchecked_mut(index).
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
    Err(ErrorKind::InvalidPathContent(parent.path.clone()).into())
}

fn insert_leaf(parent: Arc<RefCell<Node>>, label: &str, ty: NodeType) -> Result<()> {
    let mut path = parent.borrow().path.clone();
    if path.len() != 1 {
        // We aren't at the root.
        path.push_str("/");
    }
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
    use errors::*;
    use containers::Container;

    #[test]
    fn create_nodes() {
        let original_tree = Tree::new();
        assert_eq!(original_tree.root.borrow().version, 0);
        let tree = original_tree.create("/somenode", NodeType::Directory).unwrap();
        assert_eq!(tree.root.borrow().version, 1);
        let tree = tree.create("/somenode/somechildnode", NodeType::Set).unwrap();
        assert_eq!(tree.root.borrow().version, 2);
        let tree = tree.create("/somedir1/somedir2/leaf", NodeType::Queue).unwrap();
        assert_eq!(tree.root.borrow().version, 3);
        assert_eq!(original_tree.root.borrow().version, 0);
        if let Content::Directory(ref edges) = tree.root.borrow().content {
            assert_eq!(edges.len(), 2);
            assert_eq!(edges[0].label, "somedir1".to_string());
            assert_eq!(edges[1].label, "somenode".to_string());
            assert_eq!(edges[1].node.borrow().version, 1);
            assert_eq!(edges[0].node.borrow().version, 0);
            if let Content::Directory(ref edges) = edges[1].node.borrow().content {
                assert_eq!(edges.len(), 1);
                assert_eq!(edges[0].label, "somechildnode".to_string());
                assert_eq!(edges[0].node.borrow().version, 0);
                assert_eq!(edges[0].node.borrow().path, "/somenode/somechildnode".to_string());
                assert_matches!(edges[0].node.borrow().content, Content::Container(Container::Set(_)));
            } else {
                assert!(false);
            }
            if let Content::Directory(ref edges) = edges[0].node.borrow().content {
                assert_eq!(edges.len(), 1);
                assert_eq!(edges[0].label, "somedir2".to_string());
                assert_eq!(edges[0].node.borrow().version, 0);
                assert_eq!(edges[0].node.borrow().path, "/somedir1/somedir2".to_string());
                if let Content::Directory(ref edges) = edges[0].node.borrow().content {
                    assert_eq!(edges.len(), 1);
                    assert_eq!(edges[0].label, "leaf");
                    assert_eq!(edges[0].node.borrow().version, 0);
                    assert_eq!(edges[0].node.borrow().path, "/somedir1/somedir2/leaf".to_string());
                    assert_matches!(edges[0].node.borrow().content,
                                    Content::Container(Container::Queue(_)));
                }
            } else {
                assert!(false)
            }
        } else {
            assert!(false);
        }
        let err = tree.create("/somenode/somechildnode", NodeType::Set).unwrap_err();
        assert_matches!(*err.kind(), ErrorKind::AlreadyExists(_));
        let err = tree.create("blahblah", NodeType::Set).unwrap_err();
        assert_matches!(*err.kind(), ErrorKind::BadPath(_));
        let err = tree.create("/somenode/somechildnode/leaf", NodeType::Set).unwrap_err();
        assert_matches!(*err.kind(), ErrorKind::InvalidPathContent(_));
    }

    #[test]
    fn create_nodes_iter_check() {
        let tree = Tree::new();
        let tree = tree.create("/somenode", NodeType::Directory).unwrap();
        let tree = tree.create("/somenode/somechildnode", NodeType::Set).unwrap();
        let tree = tree.create("/somedir1/somedir2/leaf", NodeType::Queue).unwrap();

        // Tuples are (path, num_edges, version)
        // Num edges is  None if not a directory
        // Note the sorted order
        let expected = [("/", Some(2), 3),
                        ("/somedir1", Some(1), 0),
                        ("/somedir1/somedir2", Some(1), 0),
                        ("/somedir1/somedir2/leaf", None, 0),
                        ("/somenode", Some(1), 1),
                        ("/somenode/somechildnode", None, 0)];

        // All the directories and leaves including "/"
        assert_eq!(tree.iter().count(), expected.len());
        for (i, node) in tree.iter().enumerate() {
            let (path, num_edges, version) = expected[i];
            assert_eq!(node.path, path);
            assert_eq!(node.version, version);
            if let Some(num_edges) = num_edges {
                if let IterContent::Directory(ref labels) = node.content {
                    assert_eq!(labels.len(), num_edges);
                } else {
                    assert!(false);
                }
            }
        }
    }
}
