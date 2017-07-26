use node::NodeType;

/// A Guard on a CAS operation
///
/// A guard is true if the current version of the node at `path` is the same as `version`.
#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct Guard {
    pub path: String,
    pub version: u64
}

/// A write operation that is part of a multi-cas
#[derive(Debug, Clone)]
pub enum WriteOp {
    CreateNode { path: String, ty: NodeType },
    DeleteNode { path: String },
    BlobPut { path: String, val: Vec<u8> },
    QueuePush { path: String, val: Vec<u8> },
    QueuePop { path: String },
    SetInsert { path: String, val: Vec<u8> },
    SetRemove { path: String, val: Vec<u8> },
    Snapshot { directory: String }
}

#[cfg(test)]
mod tests {
    use quickcheck::{Arbitrary, Gen};
    use tree::{Tree, Reply};
    use node::NodeType;
    use super::WriteOp;
    use rand::distributions::range::Range;
    use rand::distributions::IndependentSample;
    use arbitrary::Path;

    #[cfg_attr(rustfmt, rustfmt_skip)]
    impl Arbitrary for WriteOp {
        fn arbitrary<G: Gen>(g: &mut G) -> WriteOp {
            let range = Range::new(1u8, 8u8);
            let path = Path::arbitrary(g).0;
            let mut val: Vec<u8> = vec![0; 5];
            g.fill_bytes(&mut val);
            match range.ind_sample(g) {
                1 => WriteOp::CreateNode {path: path, ty: NodeType::arbitrary(g)},
                2 => WriteOp::DeleteNode {path: path},
                3 => WriteOp::BlobPut {path: path, val: val},
                4 => WriteOp::QueuePush {path: path, val: val},
                5 => WriteOp::QueuePop {path: path},
                6 => WriteOp::SetInsert {path: path, val: val},
                7 => WriteOp::SetRemove {path: path, val: val},
                _ => unreachable!()
            }
        }
    }

    /// Generate a bunch of write operations. Run them one at a time and filter out failing
    /// operations. Then run the whole set as a multi-cas. Ensure the output is the same between the
    /// ops run in the multicas and one at a time.
    quickcheck! {
        fn prop_multi_cas_equals_individual_ops(ops: Vec<WriteOp>) -> bool {
            let tree = Tree::new();
            let (filtered_ops, individual_replies, individual_tree) = filter_by_valid(ops);
            let (replies, new_tree) = tree.multi_cas(vec![], filtered_ops).unwrap();
            new_tree.iter().zip(individual_tree.iter())
                .all(|(node1, node2)| node1 == node2) && (replies == individual_replies)
        }
    }

    /// Any op that doesn't succeed on it's own is removed from the list
    fn filter_by_valid<'a>(ops: Vec<WriteOp>) -> (Vec<WriteOp>, Vec<Reply>, Tree) {
        ops.into_iter()
           .fold((Vec::new(), Vec::new(), Tree::new()), |(mut ops, mut replies, tree), op| {
            match tree.multi_cas(vec![], vec![op.clone()]) {
                Ok((new_replies, new_tree)) => {
                    ops.push(op);
                    replies.extend(new_replies);
                    (ops, replies, new_tree)
                }
                Err(_) => (ops, replies, tree),
            }
        })
    }
}
