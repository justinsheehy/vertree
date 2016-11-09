// Used by containers/Set
// See https://github.com/rust-lang/rust/issues/34511
#![feature(conservative_impl_trait)]

// Used by serde
#![feature(proc_macro)]

#[macro_use]
extern crate error_chain;

#[cfg(test)]
#[macro_use]
extern crate assert_matches;

extern crate rmp as msgpack;

#[macro_use]
extern crate serde_derive;


mod errors;
pub mod containers;

use std::sync::Arc;
use std::cell::RefCell;
use std::collections::HashSet;
use std::io::{Read, Seek, SeekFrom};
use std::error::Error;
use std::fs::File;
use errors::{Result, ErrorKind};
use containers::{Container, Blob, BlobOp, Queue, QueueOp, Set, SetOp, Value, Reply, Op};

// Types of Content - Used for msgpack serialization
const DIRECTORY_TYPE_ID: u8 = 0;
const CONTAINER_TYPE_ID: u8 = 1;

// Types of containers - Used for msgpack serialization
const BLOB_TYPE_ID: u8 = 0;
const QUEUE_TYPE_ID: u8 = 1;
const SET_TYPE_ID: u8 = 2;

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
    root: Arc<RefCell<Node>>,
    depth: usize
}

impl Tree {
    pub fn new() -> Tree {
        Tree {
            root: Arc::new(RefCell::new(Node::new("/", Content::Directory(vec![])))),
            depth: 1
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
    pub fn create(&self, path: &str, ty: NodeType) -> Result<Tree> {
        let path = try!(validate_path(path));
        let root = cow_node(&self.root);
        let mut node = root.clone();
        let mut iter = path.split('/').peekable();
        let mut depth = 1;
        while let Some(s) = iter.next() {
            if iter.peek().is_none() {
                // This is the last component in the path
                try!(insert_leaf(node.clone(), &s, ty));
                depth += 1;
                break;
            }
            node = try!(insert_dir(node.clone(), &s));
            depth += 1;
        }
        return Ok(Tree {root: root, depth: depth})
    }

    pub fn iter(&self) -> Iter {
        Iter {
            stack: vec![&self.root]
        }
    }

    pub fn path_iter<'a>(&'a self, paths: Vec<&'a str>) -> PathIter<'a> {
        PathIter::new(&self.root, paths, self.depth)
    }

    /// Run an operation on parts of the tree.
    ///
    /// An operation may utilize multiple nodes in the tree.
    /// Readable operations don't perform any copies or allocations.
    /// Writable operations perform path copies and return the new tree.
    pub fn run(&self, op: Op) -> Result<(Reply, Option<Tree>)> {
        if op.is_write() {
            return self.update(op);
        }
        let reply = try!(self.read(op));
        Ok((reply, None))
    }

    /// Write a snapshot of a tree to the directory `dir` in MsgPack format.
    ///
    /// Return the number of nodes written on success.
    ///
    /// The format of a filename is vertree_<RootVersion>.tree
    /// Note that taking a snapshot of an identical tree will overwrite the previously written file.
    pub fn snapshot<F>(&self, dir: &str) -> Result<(usize)> {
        let dir = dir.trim_right_matches("/");
        let filename = format!("{}/vertree_{}.tree", dir, self.root.borrow().version);
        let mut f = try!(File::create(filename));
        let iter = self.iter();
        let mut count = 0;
        for node in iter {
           count += 1;
           try!(write_node(&mut f, &node));
        }
        Ok(count)
    }

    fn update(&self, op: Op) -> Result<(Reply, Option<Tree>)> {
        match op {
            Op::Blob(op) => self.write_blob(op),
            Op::Queue(op) => self.write_queue(op),
            Op::Set(op) => self.write_set(op)
        }
    }

    fn read(&self, op: Op) -> Result<Reply> {
        match op {
            Op::Blob(op) => self.read_blob(op),
            Op::Queue(op) => self.read_queue(op),
            Op::Set(op) => self.read_set(op)
        }
    }

    fn write_blob(&self, op: BlobOp) -> Result<(Reply, Option<Tree>)> {
        if let BlobOp::Put { path, val } = op {
            let path = try!(validate_path(&path));
            let (node, tree) = try!(self.find_mut(&path, NodeType::Blob));
            node.content = Content::Container(Container::Blob(Blob { data: val }));
            let reply = Reply {
                // Return the normalized string (trailing slashes removed) as done here?
                path: Some(path.to_string()),
                version: Some(node.version),
                value: Value::None
            };
            return Ok((reply, Some(tree)));
        }
        unreachable!();
    }

    fn write_queue(&self, op: QueueOp) -> Result<(Reply, Option<Tree>)> {
        match op {
            QueueOp::Push { path, val } => {
                let (mut queue, version, tree) = try!(self.get_queue_mut(&path));
                queue.push(val);
                let reply = Reply {
                    path: Some(path),
                    version: Some(version),
                    value: Value::None
                };
                Ok((reply, Some(tree)))
            },
            QueueOp::Pop { path } => {
                let (mut queue, version, tree) = try!(self.get_queue_mut(&path));
                let reply = Reply {
                    path: Some(path),
                    version: Some(version),
                    value: queue.pop().map_or(Value::None, |blob| Value::OwnedBlob(blob))
                };
                Ok((reply, Some(tree)))
            },
            _ => unreachable!()
        }
    }

    fn write_set(&self, op: SetOp) -> Result<(Reply, Option<Tree>)> {
        match op {
            SetOp::Insert { path, val } => {
                let (mut set, version, tree) = try!(self.get_set_mut(&path));
                let reply = Reply {
                    path: Some(path),
                    version: Some(version),
                    value: Value::Bool(set.insert(val))
                };
                Ok((reply, Some(tree)))
            },
            SetOp::Remove { path, val } => {
                let (mut set, version, tree) = try!(self.get_set_mut(&path));
                let reply = Reply {
                    path: Some(path),
                    version: Some(version),
                    value: Value::Bool(set.remove(&val))
                };
                Ok((reply, Some(tree)))
            },
            _ => unreachable!()
        }
    }

    fn get_queue_mut(&self, path: &str) -> Result<(&mut Queue, usize, Tree)> {
        let path = try!(validate_path(&path));
        let (node, tree) = try!(self.find_mut(&path, NodeType::Queue));
        let mut queue = node.content.get_queue_mut().unwrap();
        Ok((queue, node.version, tree))
    }

    fn get_set_mut(&self, path: &str) -> Result<(&mut Set, usize, Tree)> {
        let path = try!(validate_path(&path));
        let (node, tree) = try!(self.find_mut(&path, NodeType::Set));
        let mut queue = node.content.get_set_mut().unwrap();
        Ok((queue, node.version, tree))
    }

    fn read_blob(&self, op: BlobOp) -> Result<Reply> {
        let reply = match op {
            BlobOp::Get {path} => {
                let (blob, version) = try!(self.find_blob(&path));
                Reply {
                    path: Some(path),
                    version: Some(version),
                    value: Value::Blob(blob)
                }
            },
            BlobOp::Len {path} => {
                let (blob, version) = try!(self.find_blob(&path));
                Reply  {
                    path: Some(path),
                    version: Some(version),
                    value: Value::Int(blob.len())
                }
            },
            _ => unreachable!()
        };
        Ok(reply)
    }

    fn read_queue(&self, op: QueueOp) -> Result<Reply> {
        let reply = match op {
            QueueOp::Front {path} => {
                let (queue, version) = try!(self.find_queue(&path));
                Reply {
                    path: Some(path),
                    version: Some(version),
                    value: queue.front().map_or(Value::None, |b| Value::Blob(b))
                }
            },
            QueueOp::Back {path} => {
                let (queue, version) = try!(self.find_queue(&path));
                Reply {
                    path: Some(path),
                    version: Some(version),
                    value: queue.back().map_or(Value::None, |b| Value::Blob(b))
                }
            },
            QueueOp::Len {path} => {
                let (queue, version) = try!(self.find_queue(&path));
                Reply {
                    path: Some(path),
                    version: Some(version),
                    value: Value::Int(queue.len())
                }
            },
            _ => unreachable!()
        };
        Ok(reply)
    }

    fn read_set(&self, op: SetOp) -> Result<Reply> {
        match op {
            SetOp::Contains { path, val } => {
                let (set, version) = try!(self.find_set(&path));
                Ok(Reply {
                    path: Some(path),
                    version: Some(version),
                    value: Value::Bool(set.contains(&val))
                })
            },
            SetOp::Subset { path1, path2, set } => {
                self.subset_or_superset("Subset", path1, path2, set, |set1, set2| {
                    set1.is_subset(set2)
                })
            },
            SetOp::Superset { path1, path2, set } => {
                self.subset_or_superset("Superset", path1, path2, set, |set1, set2| {
                    set1.is_superset(set2)
                })
            },
            SetOp::Union { paths, sets } => {
                self.set_op(paths, sets, |set1, set2| {
                    Set::fill(set1.union(set2).cloned().collect())
                })
            },
            SetOp::Intersection { paths, sets } => {
                self.set_op(paths, sets, |set1, set2| {
                    Set::fill(set1.intersection(set2).cloned().collect())
                })
            },
            SetOp::Difference { paths, sets } => {
                self.set_op(paths, sets, |set1, set2| {
                    Set::fill(set1.difference(set2).cloned().collect())
                })
            },
            SetOp::SymmetricDifference { paths, sets } => {
                self.set_op(paths, sets, |set1, set2| {
                    Set::fill(set1.difference(set2).cloned().collect())
                })
            }
            _ => unreachable!()
        }
    }

    fn subset_or_superset<F>(&self,
                             op: &str,
                             path1: String,
                             path2: Option<String>,
                             set: Option<HashSet<Blob>>,
                             f: F) -> Result<Reply>
        where F: Fn(&Set, &Set) -> bool
    {
        if path2.is_some() && set.is_some() {
            return Err(format!("{} can only operate on 2 sets.
                                One of `path2` or `set` must be `None`", op).into())
        }
        let (set1, _) = try!(self.find_set(&path1));

        let val = if path2.is_some() {
            let (set2, _) = try!(self.find_set(&path2.unwrap()));
            f(set1, set2)
        } else {
            f(set1, &Set::fill(set.unwrap()))

        };

        Ok(Reply {
            path: None,
            version: None,
            value: Value::Bool(val)
           })
    }


    fn set_op<F>(&self, paths: Vec<String>, sets: Vec<HashSet<Blob>>, f: F) -> Result<Reply>
        where F: Fn(Set, &Set) -> Set
    {
        let iter = self.path_iter(paths.iter().map(|path| path as &str).collect());
        let mut result = Set::new();
        for node in iter {
            let node = try!(node);
            if let Some(set) = node.content.get_set() {
                result = f(result, set);
            } else {
                return Err(ErrorKind::WrongType(node.path.clone(), node.get_type()).into());
            }
        }

        for set in sets {
            let set = Set::fill(set);
            result = f(result, &set);
        }

        Ok(Reply {
            path: None,
            version: None,
            value: Value::OwnedSet(result)
        })
    }

    fn find_blob(&self, path: &str) -> Result<(&Blob, usize)> {
        let (content, version) = try!(self.find(path, NodeType::Blob));
        Ok((content.get_blob().unwrap(), version))
    }

    fn find_queue(&self, path: &str) -> Result<(&Queue, usize)> {
        let (content, version) = try!(self.find(path, NodeType::Queue));
        Ok((content.get_queue().unwrap(), version))
    }

    fn find_set(&self, path: &str) -> Result<(&Set, usize)> {
        let (content, version) = try!(self.find(path, NodeType::Set));
        Ok((content.get_set().unwrap(), version))
    }

    /// Walk the tree until the desired node at `path` is found.
    ///
    /// Return the content and its version or an error if any part of the path doesn't exist or the
    /// node at `path` is of the wrong type.
    fn find(&self, path: &str, ty: NodeType) -> Result<(&Content, usize)> {
        let mut parent = &self.root;
        let mut iter = path.split('/').peekable();
        while let Some(s) = iter.next() {
            unsafe {
                if let Content::Directory(ref edges) = (*parent.as_ptr()).content {
                    if let Ok(index) = edges.binary_search_by_key(&s, |e| &e.label) {
                        if iter.peek().is_none() {
                            let node = &(*edges.get_unchecked(index).node.as_ptr());
                            try!(verify_type(node, ty));
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

    /// Walk the tree until the desired node at `path` is found.
    ///
    /// Copy the entire path to create a new tree. Return a mutable refernce to the Node at
    /// `path` along with the new Tree on success. Return an error if any part of the path doesn't
    /// exist or the node at `path` is of the wrong type.
    fn find_mut(&self, path: &str, ty: NodeType) -> Result<(&mut Node, Tree)> {
        let root = cow_node(&self.root);
        let mut node = root.clone();
        let mut iter = path.split('/').peekable();
        while let Some(s) = iter.next() {
            unsafe {
                if let Content::Directory(ref mut edges) = (*node.as_ptr()).content {
                    if let Ok(index) = edges.binary_search_by_key(&s, |e| &e.label) {
                        let mut edge = edges.get_unchecked_mut(index);
                        node = cow_node(&edge.node);
                        edge.node = node.clone();
                        if iter.peek().is_none() {
                            try!(verify_type(&*node.borrow(), ty));
                            return Ok((&mut *node.as_ptr(), Tree {root: root, depth: self.depth}))
                        }
                        continue;
                    } else {
                        let path = join_path(&node.borrow().path, s);
                        return Err(ErrorKind::DoesNotExist(path).into());
                    }
                }
            }
            return Err(ErrorKind::InvalidPathContent(node.borrow().path.clone()).into());
        }
        unreachable!();
    }
}

fn verify_type(node: &Node, ty: NodeType) -> Result<()> {
    let node_ty = node.get_type();
    if node_ty != ty {
        return Err(ErrorKind::WrongType(node.path.clone(), node_ty).into());
    }
    Ok(())
}

fn join_path(dir_path: &str, label: &str) -> String {
    let mut path = dir_path.to_string();
    if path.len() != 1 {
        // We aren't at the root.
        path.push_str("/");
    }
    path.push_str(label);
    path
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

/// Iterate over a tree in order, taking the shrotest path required to return each node in `paths`.
/// Along the way copy any paths necessary to build up a new tree that allows modifications to each
/// node in paths.
pub struct CowPathIter<'a> {
    tree: Tree,
    paths: Vec<&'a str>,
    stack: Vec<*mut Node>
}

impl<'a> CowPathIter<'a> {
    pub fn new(root: &'a Arc<RefCell<Node>>,
               mut paths: Vec<&'a str>,
               max_depth: usize) -> CowPathIter<'a>
    {
        paths.sort();
        paths.dedup();
        paths.reverse();
        let mut stack = Vec::with_capacity(max_depth);
        let root = cow_node(root);
        stack.push(root.as_ptr());
        CowPathIter {
            tree: Tree {root: root, depth: max_depth},
            paths: paths,
            stack: stack
        }
    }

    /// Walk the tree to find the node living at `path`
    ///
    /// Copy the path to the node and return a mutable reference to the copied node.
    /// This implementation only performs copies while walking down the tree. Successive walks are
    /// performed from the last node, back up the tree and down other paths as necessary. Therefore,
    /// this implementation performs the minimum number of copies necessary for a COW tree.
    fn walk(&mut self) -> Result<&'a mut Node> {
        let path = self.paths.pop().unwrap();
        loop {
            unsafe {
                let mut node = *self.stack.last().unwrap();
                if path.starts_with(&(*node).path) {
                    let num_labels = (*node).path.split('/').skip_while(|&s| s == "").count();
                    let mut split = path.split('/').skip_while(|&s| s == "").skip(num_labels);
                    while let Some(label) = split.next() {
                        if label == "" {
                            // Skip Trailing slashes
                            continue;
                        }
                        node = try!(cow_get_child(node, &label));
                        self.stack.push(node);
                    }
                    return Ok(&mut *node);
                }
                // No matching prefix, back up the tree
                self.stack.pop();
            }
        }
    }

    /// Once `next` returns None a complete tree has been assembled. It can be retrieved via a call
    /// to `get_tree`.
    pub fn get_tree(&self) -> Tree {
        self.tree.clone()
    }
}

// TODO: Would it actually make sense to *only* return the content here?
// The caller should never modify the path or version
impl<'a> Iterator for CowPathIter<'a> {
    type Item = Result<&'a mut Node>;
    fn next(&mut self) -> Option<Result<&'a mut Node>> {
        if self.paths.len() == 0{
            return None;
        }
        Some(self.walk())
    }
}


/// Iterate over a tree in order, taking the shortest path required to return each node in `paths`.
pub struct PathIter<'a> {
    paths: Vec<&'a str>,
    stack: Vec<&'a Node>
}

impl<'a> PathIter<'a> {
    /// Create a new iterator for a set of given paths
    ///
    /// Allocate a stack to the max depth of the tree, so we don't need to resize it.
    pub fn new(root: &'a Arc<RefCell<Node>>,
               mut paths: Vec<&'a str>,
               max_depth: usize) -> PathIter<'a>
    {
        paths.sort();
        paths.dedup();
        paths.reverse();
        let mut stack = Vec::with_capacity(max_depth);
        unsafe {
            stack.push(&*root.as_ptr());
        }
        PathIter {
            paths: paths,
            stack: stack
        }
    }

    /// Walk the tree to find the node living at `path`
    fn walk(&mut self) -> Result<&'a Node> {
        let path = self.paths.pop().unwrap();
        loop {
            let mut node = *self.stack.last().unwrap();
            if path.starts_with(&node.path) {
                let num_labels = node.path.split('/').skip_while(|&s| s == "").count();
                let mut split = path.split('/').skip_while(|&s| s == "").skip(num_labels);
                while let Some(label) = split.next() {
                    if label == "" {
                        // Skip Trailing slashes
                        continue;
                    }
                    node = try!(get_child(&node, &label));
                    // Push the child on the stack
                    self.stack.push(node);
                }
                return Ok(self.stack.last().unwrap());
            }
            // No matching prefix, back up the tree
            self.stack.pop();
        }
    }
}

impl<'a> Iterator for PathIter<'a> {
    type Item = Result<&'a Node>;
    fn next(&mut self) -> Option<Result<&'a Node>> {
        if self.paths.len() == 0{
            return None;
        }
        Some(self.walk())
    }
}

/// Take a mutable parent directory node, and COW the child node given by it's label
///
/// Insert the COW'd child in the correct position and return a reference to it
unsafe fn cow_get_child<'a>(node: *mut Node, label: &'a str) -> Result<*mut Node> {
    if let Content::Directory(ref mut edges) = (*node).content {
        match edges.binary_search_by_key(&label, |e| &e.label) {
            Ok(index) => {
                let mut edge = edges.get_unchecked_mut(index);
                edge.node = cow_node(&edge.node);
                return Ok(edge.node.as_ptr());
            },
            Err(_) => {
                let mut path = (*node).path.clone();
                if &path != "/" {
                    path.push_str("/");
                }
                path.push_str(label);
                return Err(ErrorKind::DoesNotExist(path).into());
            }
        }
    }
    Err(ErrorKind::InvalidPathContent((*node).path.clone()).into())
}

/// Return a reference to a child node of a directory given the child's label
fn get_child<'a>(node: &'a Node, label: &'a str) -> Result<&'a Node> {
    if let Content::Directory(ref edges) = node.content {
        match edges.binary_search_by_key(&label, |e| &e.label) {
            Ok(index) => {
                unsafe {
                    return Ok(&*edges.get_unchecked(index).node.as_ptr());
                }
            },
            Err(_) => {
                let mut path = node.path.clone();
                if &path != "/" {
                    path.push_str("/");
                }
                path.push_str(label);
                return Err(ErrorKind::DoesNotExist(path).into());
            }
        }
    }
    Err(ErrorKind::InvalidPathContent(node.path.clone()).into())
}


/// Check for a leading slash and at least one level of depth in path.
///
/// Strip leading and trailing slashes and return normalized path as String
fn validate_path(path: &str) -> Result<&str> {
    if !path.starts_with("/") {
        return Err(ErrorKind::BadPath(format!("{} does not start with a '/'", path)).into())
    }
    let path = path.trim_matches('/');
    if path.len() == 0 {
        return Err(ErrorKind::BadPath("Path must contain at least one component".to_string())
                   .into());
    }
    Ok(path)
}

fn insert_dir(parent: Arc<RefCell<Node>>, label: &str) -> Result<Arc<RefCell<Node>>>
{
    // avoid a copy
    let parent_path = unsafe {
        &(*parent.as_ptr()).path
    };
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
                let path = join_path(parent_path, label);
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
    let path = join_path(&parent.borrow().path, label);
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

/// Read a msgpack encoded IterNode from a file and return a Node based on it
///
/// Since directories contain child pointers in Nodes, but not in IterNodes, this function allocates
/// a properly sized vector for directory entries (edges) but leaves it empty. It will be filled in
/// when reconstructing the tree.
fn read_node(file: &mut File) -> Result<Node> {
    let path_len = try!(msgpack::decode::read_str_len(file));
    let mut path_buf = vec![0u8; path_len as usize];
    let path = try!(msgpack::decode::read_str_data(file, path_len, &mut path_buf).map_err(|e| {
        e.description().to_string()
    }));
    let version = try!(msgpack::decode::read_u64_loosely(file));
    let content = try!(read_content(file));
    Ok(Node {
        path: path.to_string(),
        version: version as usize,
        content: content
    })
}

fn read_content(file: &mut File) -> Result<Content> {
    let content_type = try!(msgpack::decode::read_u8(file));
    match content_type {
        DIRECTORY_TYPE_ID => {
            let len = try!(msgpack::decode::read_array_size(file));
            for _ in 0..len {
                // Discard the labels. We will proprly fill in the edges and create pointers when we
                // reconstuct the tree. Reading them in now and decoding as utf-8 is wasteful.
                let str_len = try!(msgpack::decode::read_str_len(file));
                try!(file.seek(SeekFrom::Current(str_len as i64)));
            }
            Ok(Content::Directory(Vec::with_capacity(len as usize)))
        },
        CONTAINER_TYPE_ID => {
            let container = try!(read_container(file));
            Ok(Content::Container(container))
        },
        _ => unreachable!()
    }
}

fn read_container(file: &mut File) -> Result<Container> {
    let container_type = try!(msgpack::decode::read_u8(file));
    match container_type {
        BLOB_TYPE_ID => {
            let blob = try!(read_blob(file));
            Ok(Container::Blob(blob))
        },
        QUEUE_TYPE_ID => {
            let len = try!(msgpack::decode::read_array_size(file));
            let mut queue = Queue::with_capacity(len as usize);
            for _ in 0..len {
                let blob = try!(read_blob(file));
                queue.push(blob)
            }
            Ok(Container::Queue(queue))
        },
        SET_TYPE_ID => {
            let len = try!(msgpack::decode::read_array_size(file));
            let mut set = Set::with_capacity(len as usize);
            for _ in 0..len {
                let blob = try!(read_blob(file));
                let _ = set.insert(blob);
            }
            Ok(Container::Set(set))
        },
        _ => unreachable!()
    }
}

fn read_blob(file: &mut File) -> Result<Blob> {
    let len = try!(msgpack::decode::read_bin_len(file));
    let mut buf = vec![0u8; len as usize];
    try!(file.read_exact(&mut buf));
    Ok(Blob::fill(buf))
}

/// Serialize an IterNode and write it to the given file
///
/// This function uses the low level msgpack functions directly to avoid allocation
fn write_node(file: &mut File, node: &IterNode) -> Result<()> {
    try!(msgpack::encode::write_str_len(file, node.path.len() as u32));
    try!(msgpack::encode::write_str(file, node.path));
    try!(msgpack::encode::write_uint(file, node.version as u64));
    match node.content {
        IterContent::Directory(ref labels) => {
            try!(msgpack::encode::write_u8(file, DIRECTORY_TYPE_ID));
            try!(msgpack::encode::write_array_len(file, labels.len() as u32));
            for label in labels {
                try!(msgpack::encode::write_str_len(file, label.len() as u32));
                try!(msgpack::encode::write_str(file, label));
            }
        },
        IterContent::Container(ref container) => {
            try!(msgpack::encode::write_u8(file, CONTAINER_TYPE_ID));
            try!(write_container(file, &container));
        }
    }
    Ok(())
}

/// Serialize a Container and write it to the given file
fn write_container(file: &mut File, container: &Container) -> Result<()> {
    match *container {
        Container::Blob(ref blob) => {
            try!(msgpack::encode::write_u8(file, BLOB_TYPE_ID));
            write_blob(file, blob)
        },
        Container::Queue(ref queue) => {
            try!(msgpack::encode::write_u8(file, QUEUE_TYPE_ID));
            try!(msgpack::encode::write_array_len(file, queue.len() as u32));
            for blob in queue.data.iter() {
                try!(write_blob(file, blob));
            }
            Ok(())
        },
        Container::Set(ref set) => {
            try!(msgpack::encode::write_u8(file, SET_TYPE_ID));
            try!(msgpack::encode::write_array_len(file, set.data.len() as u32));
            for blob in set.data.iter() {
                try!(write_blob(file, blob));
            }
            Ok(())
        }
    }
}

fn write_blob(file: &mut File, blob: &Blob) -> Result<()> {
    try!(msgpack::encode::write_bin_len(file, blob.len() as u32));
    msgpack::encode::write_bin(file, &blob.data[..]).map_err(|e| e.into())
}


#[cfg(test)]
mod tests {
    use super::*;
    use errors::*;
    use containers::*;

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

    #[test]
    fn path_iter() {
        let tree = Tree::new();
        let tree = tree.create("/somenode", NodeType::Directory).unwrap();
        let tree = tree.create("/somenode/somechildnode", NodeType::Set).unwrap();
        let tree = tree.create("/somedir1/somedir2/leaf", NodeType::Queue).unwrap();

        let mut paths = vec!["/somenode/somechildnode",
                             "/somedir1/somedir2",
                             "/somedir1/somedir2/leaf",
                             "/somenode/"];


        let iter = PathIter::new(&tree.root, paths.clone(), tree.depth);
        let collected: Vec<&str> = iter.map(|node| &node.unwrap().path as &str).collect();
        paths.sort();
        let paths: Vec<&str> = paths.iter().map(|p| p.trim_right_matches('/')).collect();
        assert_eq!(paths, collected);
    }

    #[test]
    fn bad_path_iter() {
        let tree = Tree::new();
        let tree = tree.create("/somenode", NodeType::Directory).unwrap();
        let tree = tree.create("/somenode/somechildnode", NodeType::Set).unwrap();
        let tree = tree.create("/somedir1/somedir2/leaf", NodeType::Queue).unwrap();

        let paths = vec!["/somenode/somechildnode", "/zzz"];

        let mut iter = PathIter::new(&tree.root, paths, tree.depth);
        assert_matches!(iter.next(), Some(Ok(_)));
        assert_matches!(iter.next(), Some(Err(_)));
        assert_matches!(iter.next(), None);
    }

    #[test]
    fn cow_path_iter() {
        let tree = Tree::new();
        let tree = tree.create("/somenode", NodeType::Directory).unwrap();
        let tree = tree.create("/somenode/somechildnode", NodeType::Blob).unwrap();
        let tree = tree.create("/somedir1/somedir2/leaf", NodeType::Blob).unwrap();

        // 3 create calls were made
        assert_eq!(3, tree.root.borrow().version);

        let paths = vec!["/somenode/somechildnode", "/somedir1/somedir2/leaf"];
        let mut iter = CowPathIter::new(&tree.root, paths.clone(), tree.depth);

        for node in iter.by_ref() {
            let blob = Blob { data: "hello".to_string().into_bytes() };
            node.unwrap().content = Content::Container(Container::Blob(blob));
        }

        let cow_tree = iter.get_tree();

        // Original tree still unchanged
        assert_eq!(3, tree.root.borrow().version);

        // Mutation is optimal for CowPathIter even when copying multiple paths. Therefore,
        // the root version count is only incremented once.
        assert_eq!(4, cow_tree.root.borrow().version);

        // Iterate the original tree and show the empty blobs
        let iter = PathIter::new(&tree.root, paths.clone(), tree.depth);
        for node in iter {
            let node = node.unwrap();
            let blob = node.content.get_blob().unwrap();
            assert_eq!(*blob, Blob::new());
            assert_eq!(node.version, 0);
        }

        // Iterate the modified tree and show "hello"
        let iter = PathIter::new(&cow_tree.root, paths.clone(), tree.depth);
        for node in iter {
            let node = node.unwrap();
            let blob = node.content.get_blob().unwrap();
            assert_eq!(&blob.data[..], "hello".as_bytes());
            // Each node was only modified once
            assert_eq!(node.version, 1);
        }

    }
}
