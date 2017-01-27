use std::sync::Arc;
use tree::Tree;
use node::{Node, Content};
use errors::{Result, ErrorKind};
use containers::Container;

/// Deep clone a node and bump it's version
pub fn cow_node(node: &Arc<Node>) -> Arc<Node> {
    // Create a shallow copy of the node (inc ref count on Arc)
    let mut new_node = node.clone();

    // Force a deep copy on write copy and increment the version number
    Arc::make_mut(&mut new_node).version += 1;
    new_node
}

/// Directories contain a list of labels for each edge
/// Containers are an actual reference to the Container and it's data
#[derive(Eq, PartialEq)]
pub enum IterContent<'a> {
    Directory(Vec<&'a str>),
    Container(&'a Container),
}

#[derive(Eq, PartialEq)]
pub struct IterNode<'a> {
    pub path: &'a str,
    pub version: u64,
    pub content: IterContent<'a>,
}

/// An iterator that performs a depth first walk of the entire tree.
pub struct Iter<'a> {
    stack: Vec<&'a Arc<Node>>,
}

impl<'a> Iter<'a> {
    pub fn new(root: &'a Arc<Node>) -> Iter<'a> {
        Iter { stack: vec![root] }
    }
}

impl<'a> Iterator for Iter<'a> {
    type Item = IterNode<'a>;
    fn next(&mut self) -> Option<IterNode<'a>> {
        if self.stack.is_empty() {
            return None;
        }
        let node = self.stack.pop().unwrap();
        let content = match node.content {
            Content::Directory(ref edges) => {
                self.stack.extend(edges.iter().rev().map(|edge| &edge.node));
                IterContent::Directory(edges.iter().map(|edge| &edge.label as &str).collect())
            }
            Content::Container(ref container) => IterContent::Container(container),
        };
        Some(IterNode {
            path: &node.path,
            version: node.version,
            content: content,
        })
    }
}

/// Iterate over a tree in order, taking the shrotest path required to return each node in `paths`.
/// Along the way copy any paths necessary to build up a new tree that allows modifications to each
/// node in paths.
pub struct CowPathIter<'a> {
    tree: Tree,
    paths: Vec<&'a str>,
    stack: Vec<*mut Node>,
}

impl<'a> CowPathIter<'a> {
    pub fn new(root: &'a Arc<Node>, mut paths: Vec<&'a str>, max_depth: u32) -> CowPathIter<'a> {
        paths.sort();
        paths.dedup();
        paths.reverse();
        let mut stack = Vec::with_capacity(max_depth as usize);
        let root = cow_node(root);
        let ptr: *mut Node = &*root as *const Node as *mut Node;
        stack.push(ptr);
        CowPathIter {
            tree: Tree {
                root: root,
                depth: max_depth,
            },
            paths: paths,
            stack: stack,
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
                let mut node = match self.stack.last() {
                    Some(node) => *node,
                    None => return Err(ErrorKind::DoesNotExist(path.to_string()).into()),
                };
                if path.starts_with(&(*node).path) {
                    let num_labels = (*node).path.split('/').skip_while(|&s| s == "").count();
                    let split = path.split('/').skip_while(|&s| s == "").skip(num_labels);
                    for label in split {
                        if label == "" {
                            // Skip Trailing slashes
                            continue;
                        }
                        node = cow_get_child(node, label)?;
                        let ptr: *mut Node = &mut (*node);
                        self.stack.push(ptr);
                    }
                    return Ok(&mut *node);
                }
                // No matching prefix, back up the tree
                self.stack.pop();
            }
        }
    }

    /// Once `next` returns `None` a complete tree has been assembled. It can be retrieved via a call
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
        if self.paths.is_empty() {
            return None;
        }
        Some(self.walk())
    }
}


/// Iterate over a tree in order, taking the shortest path required to return each node in `paths`.
pub struct PathIter<'a> {
    paths: Vec<&'a str>,
    stack: Vec<&'a Node>,
}

impl<'a> PathIter<'a> {
    /// Create a new iterator for a set of given paths
    ///
    /// Allocate a stack to the max depth of the tree, so we don't need to resize it.
    pub fn new(root: &'a Arc<Node>, mut paths: Vec<&'a str>, max_depth: u32) -> PathIter<'a> {
        paths.sort();
        paths.dedup();
        paths.reverse();
        let mut stack = Vec::with_capacity(max_depth as usize);
        let node_ref: &Node = &*root;
        stack.push(node_ref);
        PathIter {
            paths: paths,
            stack: stack,
        }
    }

    /// Walk the tree to find the node living at `path`
    fn walk(&mut self) -> Result<&'a Node> {
        let path = self.paths.pop().unwrap();
        loop {
            let mut node = match self.stack.last() {
                Some(node) => *node,
                None => return Err(ErrorKind::DoesNotExist(path.to_string()).into()),
            };
            if path.starts_with(&node.path) {
                let num_labels = node.path.split('/').skip_while(|&s| s == "").count();
                let split = path.split('/').skip_while(|&s| s == "").skip(num_labels);
                let mut depth_from_current_node = 0;
                for label in split {
                    depth_from_current_node += 1;
                    if label == "" {
                        // Skip Trailing slashes
                        continue;
                    }
                    node = get_child(node, label)?;
                    // Push the child on the stack
                    self.stack.push(node);
                }
                if depth_from_current_node > 0 {
                    // This path we are trying to find is a child of this node
                    return Ok(self.stack.last().unwrap());
                }
            }
            // No matching prefix, back up the tree
            self.stack.pop();
        }
    }
}

impl<'a> Iterator for PathIter<'a> {
    type Item = Result<&'a Node>;
    fn next(&mut self) -> Option<Result<&'a Node>> {
        if self.paths.is_empty() {
            return None;
        }
        Some(self.walk())
    }
}

/// Take a mutable parent directory node, and COW the child node given by it's label
///
/// Insert the COW'd child in the correct position and return a reference to it
unsafe fn cow_get_child(node: *mut Node, label: &str) -> Result<*mut Node> {
    if let Content::Directory(ref mut edges) = (*node).content {
        match edges.binary_search_by_key(&label, |e| &e.label) {
            Ok(index) => {
                let mut edge = edges.get_unchecked_mut(index);
                edge.node = cow_node(&edge.node);
                let ptr: *mut Node = &*edge.node as *const Node as *mut Node;
                return Ok(ptr);
            }
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
            Ok(index) => unsafe {
                return Ok(&*edges.get_unchecked(index).node);
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

#[cfg(test)]
mod tests {
    use super::*;
    use tree::Tree;
    use node::*;
    use containers::*;
    use arbitrary::Path;

    quickcheck! {
        // Walking any existing paths always succeeds.
        fn prop_walk_existing_paths(node_specs: Vec<(Path, NodeType)>) -> bool {
            // Get the new tree and any node_specs where create succeeded
            let (tree, node_specs) =
                node_specs.iter().fold((Tree::new(),
                                        Vec::new()),
                                        |(tree, mut specs), &(ref path, node_type)|
                {
                    match tree.create(&path.clone().0, node_type) {
                        Ok(new_tree) => {
                            specs.push((path.clone(), node_type));
                            (new_tree, specs)
                        },
                        Err(_) => (tree, specs)
                    }
                });
            if node_specs.len() as u64 != tree.root.version {
                return false;
            }

            // Ensure we can find nodes at all inserted paths
            if node_specs.iter().any(|&(ref path, ty)| tree.find(&path.0, ty).is_err()) {
                return false;
            }

            // Ensure we can walk all inserted paths using a PathIter
            let paths = node_specs.iter().map(|&(ref path, _)| &path.0 as &str).collect();
            tree.path_iter(paths).count() == node_specs.len()
        }
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
        assert_eq!(3, tree.root.version);

        let paths = vec!["/somenode/somechildnode", "/somedir1/somedir2/leaf"];
        let mut iter = CowPathIter::new(&tree.root, paths.clone(), tree.depth);

        for node in iter.by_ref() {
            let blob = "hello".to_string().into_bytes();
            node.unwrap().content = Content::Container(Container::Blob(blob));
        }

        let cow_tree = iter.get_tree();

        // Original tree still unchanged
        assert_eq!(3, tree.root.version);

        // Mutation is optimal for CowPathIter even when copying multiple paths. Therefore,
        // the root version count is only incremented once.
        assert_eq!(4, cow_tree.root.version);

        // Iterate the original tree and show the empty blobs
        let iter = PathIter::new(&tree.root, paths.clone(), tree.depth);
        for node in iter {
            let node = node.unwrap();
            let blob = node.content.get_blob().unwrap();
            assert_eq!(blob.len(), 0);
            assert_eq!(node.version, 0);
        }

        // Iterate the modified tree and show "hello"
        let iter = PathIter::new(&cow_tree.root, paths.clone(), tree.depth);
        for node in iter {
            let node = node.unwrap();
            let blob = node.content.get_blob().unwrap();
            assert_eq!(&blob[..], "hello".as_bytes());
            // Each node was only modified once
            assert_eq!(node.version, 1);
        }

    }
}
