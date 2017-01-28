use msgpack::decode::{read_u32, read_u8, read_str_len, read_str_data, read_u64_loosely};
use msgpack::decode::{read_array_size, read_bin_len, ValueReadError, ReadError};
use msgpack::encode::{write_u32, write_u8, write_str, write_uint, write_array_len, write_bin};

use std::io::{Write, Read, Seek, SeekFrom};
use std::error::Error;
use std::sync::Arc;
use errors::Result;
use tree::Tree;
use iterators::{Iter, IterNode, IterContent};
use node::{Node, Content, Edge};
use containers::{Container, Queue, Set};

// Types of Content - Used for msgpack serialization
const DIRECTORY_TYPE_ID: u8 = 0;
const CONTAINER_TYPE_ID: u8 = 1;

// Types of containers - Used for msgpack serialization
const BLOB_TYPE_ID: u8 = 0;
const QUEUE_TYPE_ID: u8 = 1;
const SET_TYPE_ID: u8 = 2;

/// Write a snapshot to a Writer `W`
///
/// Return the number of nodes written on success
pub fn write<W: Write>(writer: &mut W, depth: u32, iter: Iter) -> Result<()> {
    write_u32(writer, depth)?;
    for node in iter {
        write_node(writer, &node)?;
    }
    Ok(())
}

/// Load a tree from a Reader `R`
pub fn load<R>(reader: &mut R) -> Result<Tree> where R: Read + Seek {
    let depth = read_u32(reader)?;
    let root = read_node(reader)?;
    if root.is_none() {
        return Err("empty tree".into());
    }
    let root = Arc::new(root.unwrap());
    read_inner_nodes(root.clone(), reader, depth)?;
    // We are done reading the file
    Ok(Tree { root: root, depth: depth })}

fn read_inner_nodes<R>(root: Arc<Node>, reader: &mut R, depth: u32) -> Result<()>
    where R: Read + Seek
{
    // A stack of directories for a depth first traversal
    let mut stack = Vec::with_capacity(depth as usize);
    stack.push(root);
    loop {
        match read_node(reader) {
            Ok(Some(node)) => {
                let node = Arc::new(node);
                let node_depth = node.path.split('/').skip_while(|&s| s == "").count();
                while node_depth != stack.len() {
                    stack.pop();
                }
                // This node is a child of the current top of the stack
                // Unsafe because insert_edge mutates an Arc (the parent of this node)
                // It's safe in our case because there is no concurrency
                unsafe {
                    insert_edge(&mut stack, node.clone());
                }

                // If the last node pushed is a directory, then add it to the stack
                if node.content.is_dir() {
                    stack.push(node);
                }
            },
            Ok(None) => return Ok(()),
            Err(e) => return Err(e)
        }
    }
}

/// Serialize an `IterNode` and write it to `W`
///
/// This function uses the low level msgpack functions directly to avoid allocation
fn write_node<W: Write>(writer: &mut W, node: &IterNode) -> Result<()> {
    write_str(writer, node.path)?;
    write_uint(writer, node.version as u64)?;
    match node.content {
        IterContent::Directory(ref labels) => {
            write_u8(writer, DIRECTORY_TYPE_ID)?;
            write_array_len(writer, labels.len() as u32)?;
            for label in labels {
                write_str(writer, label)?;
            }
        },
        IterContent::Container(container) => {
            write_u8(writer, CONTAINER_TYPE_ID)?;
            write_container(writer, container)?;
        }
    }
    Ok(())
}

/// Read a msgpack encoded `IterNode` from a file and return a Node based on it
///
/// Since directories contain child pointers in Nodes, but not in `IterNode`s, this function allocates
/// a properly sized vector for directory entries (edges) but leaves it empty. It will be filled in
/// when reconstructing the tree.
fn read_node<R>(reader: &mut R) -> Result<Option<Node>> where R: Read + Seek {
    match read_str_len(reader) {
        Ok(path_len) => {
            let mut path_buf = vec![0u8; path_len as usize];
            let path = read_str_data(reader, path_len, &mut path_buf).map_err(|e| {
                e.cause().unwrap().to_string()
            })?;
            let version = read_u64_loosely(reader)?;
            let content = read_content(reader)?;
            Ok(Some(Node {
                path: path.to_string(),
                version: version,
                content: content
            }))
        },
        Err(ValueReadError::InvalidMarkerRead(ReadError::UnexpectedEOF)) => Ok(None),
        Err(e) => Err(e.into())
    }
}

fn read_content<R>(reader: &mut R) -> Result<Content> where R: Read + Seek {
    let content_type = read_u8(reader)?;
    match content_type {
        DIRECTORY_TYPE_ID => {
            let len = read_array_size(reader)?;
            for _ in 0..len {
                // Discard the labels. We will proprly fill in the edges and create pointers when we
                // reconstuct the tree. Reading them in now and decoding as utf-8 is wasteful.
                let str_len = read_str_len(reader)?;
                reader.seek(SeekFrom::Current(str_len as i64))?;
            }
            Ok(Content::Directory(Vec::with_capacity(len as usize)))
        },
        CONTAINER_TYPE_ID => {
            let container = read_container(reader)?;
            Ok(Content::Container(container))
        },
        _ => unreachable!()
    }
}

fn read_container<R: Read>(reader: &mut R) -> Result<Container> {
    let container_type = read_u8(reader)?;
    match container_type {
        BLOB_TYPE_ID => {
            let blob = read_blob(reader)?;
            Ok(Container::Blob(blob))
        },
        QUEUE_TYPE_ID => {
            let len = read_array_size(reader)?;
            let mut queue = Queue::with_capacity(len as usize);
            for _ in 0..len {
                let blob = read_blob(reader)?;
                queue.push(blob)
            }
            Ok(Container::Queue(queue))
        },
        SET_TYPE_ID => {
            let len = read_array_size(reader)?;
            let mut set = Set::with_capacity(len as usize);
            for _ in 0..len {
                let blob = read_blob(reader)?;
                let _ = set.insert(blob);
            }
            Ok(Container::Set(set))
        },
        _ => unreachable!()
    }
}

fn read_blob<R: Read>(reader: &mut R) -> Result<Vec<u8>> {
    let len = read_bin_len(reader)?;
    let mut buf = vec![0u8; len as usize];
    reader.read_exact(&mut buf)?;
    Ok(buf)
}

/// Serialize a Container and write it to the given file
fn write_container<W: Write>(writer: &mut W, container: &Container) -> Result<()> {
    match *container {
        Container::Blob(ref blob) => {
            write_u8(writer, BLOB_TYPE_ID)?;
            write_blob(writer, blob)
        },
        Container::Queue(ref queue) => {
            write_u8(writer, QUEUE_TYPE_ID)?;
            write_array_len(writer, queue.len() as u32)?;
            for blob in &queue.data {
                write_blob(writer, blob)?;
            }
            Ok(())
        },
        Container::Set(ref set) => {
            write_u8(writer, SET_TYPE_ID)?;
            write_array_len(writer, set.data.len() as u32)?;
            for blob in &set.data {
                write_blob(writer, blob)?;
            }
            Ok(())
        }
    }
}

fn write_blob<W: Write>(writer: &mut W, blob: &[u8]) -> Result<()> {
    write_bin(writer, blob).map_err(|e| e.into())
}

unsafe fn insert_edge(stack: &mut Vec<Arc<Node>>, node: Arc<Node>) {
    let parent: *mut Node = &**stack.last_mut().unwrap() as *const Node as *mut Node;
    let mut edges = (*parent).content.get_dir_edges_mut().unwrap();
    let label = node.path.split('/').last().unwrap().to_string();
    let edge = Edge {
        label: label,
        node: node
    };
    edges.push(edge);
}

#[cfg(test)]
mod tests {

    use std::fs;
    use tree::Tree;
    use node::NodeType;
    use arbitrary::Path;

    /// Create a random tree, take a snapshot, and ensure reading it back in gives the same tree
    quickcheck! {
        fn prop_rountrip(node_specs: Vec<(Path, NodeType)>) -> bool {
            let tree = node_specs.iter().fold(Tree::new(), |acc, &(ref path, ref node_type)| {
                // Ignore failures. We may try to insert a node into a non-directory due to randomness
                // of generation. It doesn't matter for this property.
                match acc.create(&path.0, node_type.clone()) {
                    Ok(tree) => tree,
                    _ => acc
                }
            });
            let filename = tree.snapshot("/tmp").unwrap();
            let loaded_tree = Tree::load_snapshot(&filename).unwrap();
            fs::remove_file(filename).unwrap();

            if tree.depth != loaded_tree.depth {
                return false;
            }
            tree.iter().zip(loaded_tree.iter()).all(|(node1, node2)| node1 == node2)
        }
    }
}
