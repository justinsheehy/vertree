use quickcheck::{Arbitrary, Gen};
use rand::distributions::range::Range;
use rand::distributions::IndependentSample;
use node::NodeType;

#[derive(Debug, Clone)]
pub struct Path(pub String);

impl Arbitrary for Path {
    fn arbitrary<G: Gen>(g: &mut G) -> Path {
        let range = Range::new(1u8, 4u8);
        let depth = range.ind_sample(g);
        let labels = ['a', 'b', 'c', 'd', 'e'];
        let mut path = String::with_capacity((depth * 2 - 1) as usize);
        path = (0..depth).fold(path, |mut acc, _| {
            acc.push('/');
            acc.push(*g.choose(&labels).unwrap());
            acc
        });
        Path(path)
    }
}

impl Arbitrary for NodeType {
    fn arbitrary<G: Gen>(g: &mut G) -> NodeType {
        g.choose(&[NodeType::Directory, NodeType::Queue, NodeType::Set, NodeType::Blob])
            .unwrap()
            .clone()
    }
}
