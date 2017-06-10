use std::sync::Arc;
use std::collections::HashSet;
use std::fs::File;
use std::path::Path;
use errors::{Error, Result, ErrorKind};
use node::{Node, NodeType, Edge, Content};
use containers::{Container, Queue, Set};
use iterators::{cow_node, Iter, PathIter};
use snapshot;
use cas::{Guard, WriteOp};

/// Values included in successful replies to Operations
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Value {
    Blob(Vec<u8>),
    Set(Set),
    Int(u64),
    Bool(bool),
    Empty,
    None
}

/// The result of running an operation
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Reply {
    pub path: Option<String>,
    pub version: Option<u64>,
    pub value: Value
}

/// A hierarchical version tree.
///
/// This tree is persistent, and every update to a node both path copies the parent until it gets
/// to the root and increments the parent's version number. Only a single thread can write to the
/// tree at one time.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Tree {
    pub root: Arc<Node>,
    pub depth: u32
}

impl Tree {
    pub fn new() -> Tree {
        Tree {
            root: Arc::new(Node::new("/", Content::Directory(vec![]))),
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
        let path = validate_path(path)?;
        // Get a new root
        let root = cow_node(&self.root);
        let mut node = root.clone();
        let mut iter = path.split('/').peekable();
        let mut depth = 1;
        while let Some(s) = iter.next() {
            if iter.peek().is_none() {
                // This is the last component in the path
                unsafe {
                    // Unsafe because it mutates an Arc (the parent node)
                    // It's fine in this case, since there is no concurrency
                    insert_leaf(node.clone(), s, ty)?;
                }
                depth += 1;
                break;
            }

            unsafe {
                // Unsafe because it mutates an Arc (the parent node)
                // It's fine in this case, since there is no concurrency
                node = insert_dir(node.clone(), s)?;
            }

            depth += 1;
        }
        Ok(Tree {
            root: root,
            depth: depth
        })
    }

    pub fn delete(&self, path: &str) -> Result<(u64, Tree)> {
        if path == "/" {
            return Err(ErrorKind::CannotDeleteRoot.into());
        }

        let label = match Path::new(path).file_name() {
            Some(label) => label.to_str().unwrap(),
            None => return Err(ErrorKind::BadPath(path.to_string()).into()),
        };
        let parent = match Path::new(path).parent() {
            Some(parent) => parent.to_str().unwrap(),
            None => return Err(ErrorKind::PathMustBeAbsolute(path.to_string()).into()),
        };

        let (node, tree) = self.find_mut(parent, NodeType::Directory)?;
        if let Content::Directory(ref mut edges) =
            node.content {
            let index =
                edges.binary_search_by_key(&label, |e| &e.label)
                     .map_err(|_| Error::from(ErrorKind::DoesNotExist(path.to_string())))?;
            let deleted = edges.remove(index);
            return Ok((deleted.node.version, tree));
        }
        unreachable!()
    }

    pub fn keys(&self) -> Vec<(String, u64)> {
        self.iter()
            .map(|node| (node.path.to_string(), node.version))
            .collect()
    }

    pub fn iter(&self) -> Iter {
        Iter::new(&self.root)
    }

    pub fn path_iter<'a>(&'a self, paths: Vec<&'a str>) -> PathIter<'a> {
        PathIter::new(&self.root, paths, self.depth)
    }

    /// Write a snapshot of a tree to the directory `dir` in MsgPack format.
    ///
    /// The format of a filename is vertree_<RootVersion>.tree
    /// Note that taking a snapshot of an identical tree will overwrite the previously written file.
    /// TODO: Do this in another thread.
    pub fn snapshot(&self, dir: &str) -> Result<String> {
        let dir = dir.trim_right_matches('/');
        let filename = format!("{}/vertree_{}.tree", dir, self.root.version);
        let mut f = File::create(&filename)?;
        snapshot::write(&mut f, self)?;
        Ok(filename)
    }

    /// Load a snapshot from the file at `file`
    pub fn load_snapshot(path: &str) -> Result<Tree> {
        let mut f = File::open(path)?;
        snapshot::load(&mut f)
    }

    /// Perform a Compare and Swap operation with muliple compares and swaps
    ///
    /// Every multi_cas consists of a Vec of Guards and a Vec of Operations.
    /// Each guard contains the path and version of a node in the tree. The versions must all be the
    /// same as the nodes in the tree for the operations to run. All operations must run
    /// successfully to return a Reply and the new tree. If either a guard or op fails, then an
    /// error is returned.
    ///
    /// Some write operations, such as 'QueuePop' return values other than Ok. Due to this, we
    /// return an array of results on success.
    pub fn multi_cas(&self, guards: Vec<Guard>, ops: Vec<WriteOp>) -> Result<(Vec<Reply>, Tree)> {
        self.check_guards(guards)?;
        let mut replies = Vec::with_capacity(ops.len());
        let mut tree = self.clone();
        for op in ops {
            tree = match op {
                WriteOp::CreateNode { path, ty } => {
                    let new_tree = tree.create(&path, ty)?;
                    let version = {
                        new_tree.root.version
                    };
                    replies.push(Reply {
                                     path: Some("/".to_string()),
                                     version: Some(version),
                                     value: Value::None
                                 });
                    new_tree
                }
                WriteOp::DeleteNode { path } => {
                    let (version, new_tree) = tree.delete(&path)?;
                    replies.push(Reply {
                                     path: Some(path),
                                     version: Some(version),
                                     value: Value::None
                                 });
                    new_tree
                }
                WriteOp::BlobPut { path, val } => {
                    let (reply, new_tree) = tree.blob_put(path, val)?;
                    replies.push(reply);
                    new_tree
                }
                WriteOp::QueuePush { path, val } => {
                    let (reply, new_tree) = tree.queue_push(path, val)?;
                    replies.push(reply);
                    new_tree
                }
                WriteOp::QueuePop { path } => {
                    let (reply, new_tree) = tree.queue_pop(path)?;
                    replies.push(reply);
                    new_tree
                }
                WriteOp::SetInsert { path, val } => {
                    let (reply, new_tree) = tree.set_insert(path, val)?;
                    replies.push(reply);
                    new_tree
                }
                WriteOp::SetRemove { path, val } => {
                    let (reply, new_tree) = tree.set_remove(path, val)?;
                    replies.push(reply);
                    new_tree
                }
                WriteOp::Snapshot { directory } => {
                    let _ = tree.snapshot(&directory)?;
                    let version = {
                        tree.root.version
                    };
                    replies.push(Reply {
                                     path: Some("/".to_string()),
                                     version: Some(version),
                                     value: Value::None
                                 });
                    tree.clone()
                }
            }
        }
        Ok((replies, tree))
    }

    fn check_guards(&self, mut guards: Vec<Guard>) -> Result<()> {
        guards.sort_by_key(|g| g.path.clone());
        guards.dedup_by_key(|g| g.path.clone());
        let (paths, versions): (Vec<_>, Vec<_>) =
            guards.iter().map(|g| (&g.path as &str, g.version)).unzip();
        for (node, version) in self.path_iter(paths).zip(versions) {
            let node = node?;
            if node.version != version {
                return Err(ErrorKind::CasFailed {
                               path: node.path.clone(),
                               expected: version,
                               actual: node.version
                           }
                           .into());
            }
        }
        Ok(())
    }

    pub fn blob_put(&self, path: String, val: Vec<u8>) -> Result<(Reply, Tree)> {
        let path = validate_path(&path)?;
        let (node, tree) = self.find_mut(path, NodeType::Blob)?;
        node.content = Content::Container(Container::Blob(val));
        let reply = Reply {
            // Return the normalized string (trailing slashes removed) as done here?
            path: Some(path.to_string()),
            version: Some(node.version),
            value: Value::None
        };
        Ok((reply, tree))
    }

    pub fn queue_push(&self, path: String, val: Vec<u8>) -> Result<(Reply, Tree)> {
        let (mut queue, version, tree) = {
            let normalized = validate_path(&path)?;
            self.get_queue_mut(normalized)?
        };
        queue.push(val);
        let reply = Reply {
            path: Some(path),
            version: Some(version),
            value: Value::None
        };
        Ok((reply, tree))
    }

    pub fn queue_pop(&self, path: String) -> Result<(Reply, Tree)> {
        let (mut queue, version, tree) = {
            let normalized = validate_path(&path)?;
            self.get_queue_mut(normalized)?
        };
        let reply = Reply {
            path: Some(path),
            version: Some(version),
            value: queue.pop().map_or(Value::Empty, Value::Blob)
        };
        Ok((reply, tree))
    }

    pub fn set_insert(&self, path: String, val: Vec<u8>) -> Result<(Reply, Tree)> {
        let (mut set, version, tree) = {
            let normalized = validate_path(&path)?;
            self.get_set_mut(normalized)?
        };
        let reply = Reply {
            path: Some(path),
            version: Some(version),
            value: Value::Bool(set.insert(val))
        };
        Ok((reply, tree))
    }

    pub fn set_remove(&self, path: String, val: Vec<u8>) -> Result<(Reply, Tree)> {
        let (mut set, version, tree) = {
            let normalized = validate_path(&path)?;
            self.get_set_mut(normalized)?
        };
        let reply = Reply {
            path: Some(path),
            version: Some(version),
            value: Value::Bool(set.remove(&val))
        };
        Ok((reply, tree))
    }

    fn get_queue_mut(&self, path: &str) -> Result<(&mut Queue, u64, Tree)> {
        let (node, tree) = self.find_mut(path, NodeType::Queue)?;
        let mut queue = node.content.get_queue_mut().unwrap();
        Ok((queue, node.version, tree))
    }

    fn get_set_mut(&self, path: &str) -> Result<(&mut Set, u64, Tree)> {
        let (node, tree) = self.find_mut(path, NodeType::Set)?;
        let mut queue = node.content.get_set_mut().unwrap();
        Ok((queue, node.version, tree))
    }

    pub fn blob_get(&self, path: String) -> Result<Reply> {
        let (blob, version) = {
            let normalized = validate_path(&path)?;
            self.find_blob(normalized)?
        };
        Ok(Reply {
               path: Some(path),
               version: Some(version),
               value: Value::Blob(blob.to_vec())
           })
    }

    pub fn blob_size(&self, path: String) -> Result<Reply> {
        let (blob, version) = {
            let normalized = validate_path(&path)?;
            self.find_blob(normalized)?
        };
        Ok(Reply {
               path: Some(path),
               version: Some(version),
               value: Value::Int(blob.len() as u64)
           })
    }

    pub fn queue_front(&self, path: String) -> Result<Reply> {
        let (queue, version) = {
            let normalized = validate_path(&path)?;
            self.find_queue(normalized)?
        };
        Ok(Reply {
               path: Some(path),
               version: Some(version),
               value: queue.front()
                           .map_or(Value::Empty, |b| Value::Blob(b.clone()))
           })
    }

    pub fn queue_back(&self, path: String) -> Result<Reply> {
        let (queue, version) = {
            let normalized = validate_path(&path)?;
            self.find_queue(normalized)?
        };
        Ok(Reply {
               path: Some(path),
               version: Some(version),
               value: queue.back()
                           .map_or(Value::Empty, |b| Value::Blob(b.clone()))
           })
    }

    pub fn queue_len(&self, path: String) -> Result<Reply> {
        let (queue, version) = {
            let normalized = validate_path(&path)?;
            self.find_queue(normalized)?
        };
        Ok(Reply {
               path: Some(path),
               version: Some(version),
               value: Value::Int(queue.len() as u64)
           })
    }

    pub fn set_contains(&self, path: String, val: Vec<u8>) -> Result<Reply> {
        let (set, version) = {
            let normalized = validate_path(&path)?;
            self.find_set(normalized)?
        };
        Ok(Reply {
               path: Some(path),
               version: Some(version),
               value: Value::Bool(set.contains(&val))
           })
    }

    pub fn set_subset(&self,
                      path1: String,
                      path2: Option<String>,
                      set: Option<HashSet<Vec<u8>>>)
                      -> Result<Reply> {
        let normalized = validate_path(&path1)?;
        self.subset_or_superset("Subset", normalized, path2, set, |set1, set2| set1.is_subset(set2))
    }

    pub fn set_superset(&self,
                        path1: String,
                        path2: Option<String>,
                        set: Option<HashSet<Vec<u8>>>)
                        -> Result<Reply> {
        let normalized = validate_path(&path1)?;
        self.subset_or_superset("Superset",
                                normalized,
                                path2,
                                set,
                                |set1, set2| set1.is_superset(set2))
    }

    pub fn set_union(&self, paths: Vec<String>, sets: Vec<HashSet<Vec<u8>>>) -> Result<Reply> {
        self.set_op(paths,
                    sets,
                    |set1, set2| Set::fill(set1.union(set2).map(|s| s.to_vec()).collect()))
    }

    pub fn set_intersection(&self, path1: &str, path2: &str) -> Result<Reply> {
        self.binary_set_op(path1, path2, |set1, set2| {
            Set::fill(set1.intersection(set2).map(|s| s.to_vec()).collect())
        })
    }

    pub fn set_difference(&self, path1: &str, path2: &str) -> Result<Reply> {

        self.binary_set_op(path1, path2, |set1, set2| {
            Set::fill(set1.difference(set2).map(|s| s.to_vec()).collect())
        })
    }

    pub fn set_symmetric_difference(&self, path1: &str, path2: &str) -> Result<Reply> {
        self.binary_set_op(path1, path2, |set1, set2| {
            Set::fill(set1.symmetric_difference(set2)
                          .map(|s| s.to_vec())
                          .collect())
        })
    }


    fn subset_or_superset<F>(&self,
                             op: &str,
                             path1: &str,
                             path2: Option<String>,
                             set: Option<HashSet<Vec<u8>>>,
                             f: F)
                             -> Result<Reply>
        where F: Fn(&Set, &Set) -> bool
    {

        if path2.is_some() && set.is_some() {
            return Err(format!("{} can only operate on 2 sets.
                                One of `path2` or `set` must be `None`",
                               op)
                           .into());
        }
        let (set1, _) = self.find_set(path1)?;

        let val = if path2.is_some() {
            let (set2, _) = {
                let path2 = path2.unwrap();
                let normalized = validate_path(&path2);
                self.find_set(normalized?)?
            };
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

    fn binary_set_op<F>(&self, path1: &str, path2: &str, f: F) -> Result<Reply>
        where F: Fn(&Set, &Set) -> Set
    {
        let paths = vec![path1, path2];
        let mut iter = self.path_iter(paths.clone());
        let (node1, node2) = if let Some(node1) = iter.next() {
            if let Some(node2) = iter.next() {
                (node1?, node2?)
            } else {
                return Err(ErrorKind::DoesNotExist(path2.to_string()).into());
            }
        } else {
            return Err(ErrorKind::DoesNotExist(path1.to_string()).into());
        };

        if let Some(set1) = node1.content.get_set() {
            if let Some(set2) = node2.content.get_set() {
                let result = f(set1, set2);
                Ok(Reply {
                       path: None,
                       version: None,
                       value: Value::Set(result)
                   })
            } else {
                Err(ErrorKind::WrongType(node2.path.clone(), node2.get_type()).into())
            }
        } else {
            Err(ErrorKind::WrongType(node1.path.clone(), node1.get_type()).into())
        }

    }


    fn set_op<F>(&self, paths: Vec<String>, sets: Vec<HashSet<Vec<u8>>>, f: F) -> Result<Reply>
        where F: Fn(Set, &Set) -> Set
    {
        let paths: Vec<_> = paths.iter().map(|s| s as &str).collect();
        let iter = self.path_iter(paths.clone());
        let mut result = Set::new();
        for node in iter {
            let node = node?;
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
               value: Value::Set(result)
           })
    }

    fn find_blob(&self, path: &str) -> Result<(&[u8], u64)> {
        let (content, version) = self.find(path, NodeType::Blob)?;
        Ok((content.get_blob().unwrap(), version))
    }

    fn find_queue(&self, path: &str) -> Result<(&Queue, u64)> {
        let (content, version) = self.find(path, NodeType::Queue)?;
        Ok((content.get_queue().unwrap(), version))
    }

    fn find_set(&self, path: &str) -> Result<(&Set, u64)> {
        let (content, version) = self.find(path, NodeType::Set)?;
        Ok((content.get_set().unwrap(), version))
    }

    /// Walk the tree until the desired node at `path` is found.
    ///
    /// Return the content and its version or an error if any part of the path doesn't exist or the
    /// node at `path` is of the wrong type.
    pub fn find(&self, path: &str, ty: NodeType) -> Result<(&Content, u64)> {
        let mut parent = &self.root;
        // Trim leading empty strings and stop iterating at the first empty string after a valid
        // string
        let mut iter = path.split('/')
                           .skip_while(|s| *s == "")
                           .take_while(|s| *s != "")
                           .peekable();
        while let Some(s) = iter.next() {
            unsafe {
                if let Content::Directory(ref edges) = (*parent).content {
                    if let Ok(index) = edges.binary_search_by_key(&s, |e| &e.label) {
                        if iter.peek().is_none() {
                            let node = &(*edges.get_unchecked(index).node);
                            verify_type(node, ty)?;
                            return Ok((&node.content, node.version));
                        }
                        parent = &edges.get_unchecked(index).node;
                        continue;
                    }
                }
                return Err(ErrorKind::DoesNotExist(parent.path.clone()).into());
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
        if path == "/" {
            unsafe {
                let ptr: *mut Node = &*node as *const Node as *mut Node;
                return Ok((&mut *ptr,
                           Tree {
                               root: root,
                               depth: self.depth
                           }));
            }
        }
        // Trim leading empty strings and stop iterating at the first empty string after a valid
        // string
        let mut iter = path.split('/')
                           .skip_while(|s| *s == "")
                           .take_while(|s| *s != "")
                           .peekable();
        while let Some(s) = iter.next() {
            unsafe {
                let ptr: *mut Node = &*node as *const Node as *mut Node;
                if let Content::Directory(ref mut edges) = (*ptr).content {
                    if let Ok(index) = edges.binary_search_by_key(&s, |e| &e.label) {
                        let mut edge = edges.get_unchecked_mut(index);
                        node = cow_node(&edge.node);
                        edge.node = node.clone();
                        let ptr: *mut Node = &*node as *const Node as *mut Node;
                        if iter.peek().is_none() {
                            verify_type(&*ptr, ty)?;
                            return Ok((&mut *ptr,
                                       Tree {
                                           root: root,
                                           depth: self.depth
                                       }));
                        }
                    } else {
                        let path = join_path(&node.path, s);
                        return Err(ErrorKind::DoesNotExist(path).into());
                    }
                } else {
                    return Err(ErrorKind::InvalidPathContent(node.path.clone()).into());
                }
            }
        }
        unreachable!();
    }
}

impl Default for Tree {
    fn default() -> Self {
        Tree::new()
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

unsafe fn insert_dir(parent: Arc<Node>, label: &str) -> Result<Arc<Node>> {
    let ptr: *mut Node = &*parent as *const Node as *mut Node;
    if let Content::Directory(ref mut edges) = (*ptr).content {
        match edges.binary_search_by_key(&label, |e| &e.label) {
            Ok(index) => {
                let child = &mut edges.get_unchecked_mut(index);
                if !child.node.content.is_dir() {
                    let msg = format!("{} is a leaf node", child.node.path);
                    return Err(ErrorKind::InvalidPathContent(msg).into());
                }
                // Create a copy of child node and replace the old node
                let node = cow_node(&child.node);
                child.node = node.clone();
                return Ok(node);
            }
            Err(index) => {
                let content = Content::new(NodeType::Directory);
                // Edge doesn't exist, let's create it in the proper sort position
                let path = join_path(&parent.path, label);
                let edge = Edge::new(label, Node::new(path, content));
                let node = edge.node.clone();
                edges.insert(index, edge);
                return Ok(node);
            }
        }
    }
    Err(ErrorKind::InvalidPathContent(parent.path.clone()).into())
}

unsafe fn insert_leaf(parent: Arc<Node>, label: &str, ty: NodeType) -> Result<()> {
    let path = join_path(&parent.path, label);
    let ptr: *mut Node = &*parent as *const Node as *mut Node;
    if let Content::Directory(ref mut edges) = (*ptr).content {
        // Assume sorted vec
        if let Err(index) = edges.binary_search_by_key(&label, |e| &e.label) {
            // Edge doesn't exist, let's create it in proper sort position
            let edge = Edge::new(label, Node::new(path, Content::new(ty)));
            edges.insert(index, edge);
            return Ok(());
        }
        return Err(ErrorKind::AlreadyExists(path).into());
    }
    Err(ErrorKind::InvalidPathContent(parent.path.clone()).into())
}

/// Check for a leading slash and at least one level of depth in path.
///
/// Strip leading and trailing slashes and return normalized path as String
fn validate_path(path: &str) -> Result<&str> {
    if !path.starts_with('/') {
        return Err(ErrorKind::BadPath(format!("{} does not start with a '/'", path)).into());
    }
    let path = path.trim_matches('/');
    if path.is_empty() {
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
    fn create_and_delete_nodes() {
        let original_tree = Tree::new();
        assert_eq!(original_tree.root.version, 0);
        let tree = original_tree.create("/somenode", NodeType::Directory)
                                .unwrap();
        assert_eq!(tree.root.version, 1);
        let tree = tree.create("/somenode/somechildnode", NodeType::Set)
                       .unwrap();
        assert_eq!(tree.root.version, 2);
        let tree = tree.create("/somedir1/somedir2/leaf", NodeType::Queue)
                       .unwrap();
        assert_eq!(tree.root.version, 3);
        assert_eq!(original_tree.root.version, 0);
        if let Content::Directory(ref edges) =
            tree.root.content {
            assert_eq!(edges.len(), 2);
            assert_eq!(edges[0].label, "somedir1".to_string());
            assert_eq!(edges[1].label, "somenode".to_string());
            assert_eq!(edges[1].node.version, 1);
            assert_eq!(edges[0].node.version, 0);
            if let Content::Directory(ref edges) = edges[1].node.content {
                assert_eq!(edges.len(), 1);
                assert_eq!(edges[0].label, "somechildnode".to_string());
                assert_eq!(edges[0].node.version, 0);
                assert_eq!(edges[0].node.path, "/somenode/somechildnode".to_string());
                assert_matches!(edges[0].node.content, Content::Container(Container::Set(_)));
            } else {
                assert!(false);
            }
            if let Content::Directory(ref edges) = edges[0].node.content {
                assert_eq!(edges.len(), 1);
                assert_eq!(edges[0].label, "somedir2".to_string());
                assert_eq!(edges[0].node.version, 0);
                assert_eq!(edges[0].node.path, "/somedir1/somedir2".to_string());
                if let Content::Directory(ref edges) = edges[0].node.content {
                    assert_eq!(edges.len(), 1);
                    assert_eq!(edges[0].label, "leaf");
                    assert_eq!(edges[0].node.version, 0);
                    assert_eq!(edges[0].node.path, "/somedir1/somedir2/leaf".to_string());
                    assert_matches!(edges[0].node.content,
                                    Content::Container(Container::Queue(_)));
                }
            } else {
                assert!(false)
            }
        } else {
            assert!(false);
        }
        let err = tree.create("/somenode/somechildnode", NodeType::Set)
                      .unwrap_err();
        assert_matches!(*err.kind(), ErrorKind::AlreadyExists(_));
        let err = tree.create("blahblah", NodeType::Set).unwrap_err();
        assert_matches!(*err.kind(), ErrorKind::BadPath(_));
        let err = tree.create("/somenode/somechildnode/leaf", NodeType::Set)
                      .unwrap_err();
        assert_matches!(*err.kind(), ErrorKind::InvalidPathContent(_));
        let (_, tree) = tree.delete("/somenode/somechildnode").unwrap();
        let tree = tree.create("/somenode/somechildnode", NodeType::Set)
                       .unwrap();
        let (version, tree) = tree.delete("/somenode/somechildnode").unwrap();
        assert_eq!(0, version);
        let err = tree.delete("/somenode/somechildnode").unwrap_err();
        assert_matches!(*err.kind(), ErrorKind::DoesNotExist(_));
    }
}
