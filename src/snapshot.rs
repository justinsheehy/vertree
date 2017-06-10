use serde::{Serialize, Deserialize};
use rmp_serde::{Serializer, Deserializer};

use std::io::{Write, Read, Seek};
use errors::Result;
use tree::Tree;

/// Write a snapshot to a Writer `W`
///
/// Return the number of nodes written on success
pub fn write<W: Write>(writer: &mut W, tree: &Tree) -> Result<()> {
    let mut serializer = Serializer::new(writer);
    tree.serialize(&mut serializer)?;
    Ok(())
}

/// Load a tree from a Reader `R`
pub fn load<R>(reader: &mut R) -> Result<Tree>
    where R: Read + Seek
{
    let mut deserializer = Deserializer::new(reader);
    let tree = Tree::deserialize(&mut deserializer)?;
    Ok(tree)
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
                // Ignore failures. We may try to insert a node into a non-directory due to
                // randomness of generation. It doesn't matter for this property.
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
