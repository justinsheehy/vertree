use std::sync::Arc;
use std::cell::RefCell;
use std::collections::HashSet;
use std::fs::File;
use errors::{Result, ErrorKind};
use node::{Node, NodeType, Edge, Content};
use containers::{Container, Blob, BlobOp, Queue, QueueOp, Set, SetOp, Value, Reply, Op};
use iterators::{cow_node, Iter, PathIter};
use snapshot;

/// A hierarchical version tree.
///
/// This tree is persistent, and every update to a node both path copies the parent until it gets
/// to the root and increments the parent's version number. Only a single thread can write to the
/// tree at one time.
#[derive(Debug, Clone)]
pub struct Tree {
    pub root: Arc<RefCell<Node>>,
    pub depth: u32
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
        Iter::new(&self.root)
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
    pub fn snapshot(&self, dir: &str) -> Result<usize> {
        let dir = dir.trim_right_matches("/");
        let filename = format!("{}/vertree_{}.tree", dir, self.root.borrow().version);
        let mut f = try!(File::create(filename));
        snapshot::write(&mut f, self.depth, self.iter())
    }

    /// Load a snapshot from the file at `file`
    pub fn load_snapshot(path: &str) -> Result<Tree> {
        let mut f = try!(File::open(path));
        snapshot::load(&mut f)
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

pub fn verify_type(node: &Node, ty: NodeType) -> Result<()> {
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

#[cfg(test)]
mod tests {
    use super::*;
    use errors::*;
    use containers::*;
    use node::*;

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
}
