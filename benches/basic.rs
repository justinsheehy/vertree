#![feature(test)]

extern crate test;
extern crate vertree;

use test::Bencher;
use vertree::{Tree, NodeType};

//
// Tests of various operations on a tree with a single leaf at varying depths
//

#[bench]
fn construction(b: &mut Bencher) {
    b.iter(|| Tree::new())
}

#[bench]
fn add_leaf_at_level_1(b: &mut Bencher) {
    let tree = Tree::new();
    b.iter(|| tree.create("/foo", NodeType::Blob));
}

#[bench]
fn delete_existing_leaf_at_level_1(b: &mut Bencher) {
    let tree = Tree::new();
    let tree = tree.create("/foo", NodeType::Blob).unwrap();
    b.iter(|| tree.delete("/foo"));
}

#[bench]
fn delete_missing_leaf_at_level_1(b: &mut Bencher) {
    let tree = Tree::new();
    let tree = tree.create("/foo", NodeType::Blob).unwrap();
    b.iter(|| tree.delete("/bar"));
}

#[bench]
fn delete_missing_leaf_empty_tree(b: &mut Bencher) {
    let tree = Tree::new();
    b.iter(|| tree.delete("/bar"));
}

#[bench]
fn add_leaf_at_level_3(b: &mut Bencher) {
    let tree = Tree::new();
    b.iter(|| tree.create("/foo/bar/baz", NodeType::Blob));
}

#[bench]
fn delete_existing_leaf_at_level_3(b: &mut Bencher) {
    let tree = Tree::new();
    let tree = tree.create("/foo/bar/baz", NodeType::Blob).unwrap();
    b.iter(|| tree.delete("/foo/bar/baz"));
}

#[bench]
fn delete_missing_leaf_at_level_3(b: &mut Bencher) {
    let tree = Tree::new();
    let tree = tree.create("/foo/bar/baz", NodeType::Blob).unwrap();
    b.iter(|| tree.delete("/foo/bar/foo"));
}

#[bench]
fn delte_missing_leaf_at_level_3_empty_tree(b: &mut Bencher) {
    let tree = Tree::new();
    b.iter(|| tree.delete("/foo/bar/baz"));
}

#[bench]
fn add_leaf_level_10(b: &mut Bencher) {
    let tree = Tree::new();
    b.iter(|| tree.create("/1/2/3/4/5/6/7/8/9/10", NodeType::Blob));
}

#[bench]
fn delete_leaf_level_10(b: &mut Bencher) {
    let tree = Tree::new().create("/1/2/3/4/5/6/7/8/9/10", NodeType::Blob).unwrap();
    b.iter(|| tree.delete("/1/2/3/4/5/6/7/8/9/10"));
}

//
// Ops on trees with 10 nodes each at varying levels
//
#[bench]
fn create_10_nodes_at_level_1(b: &mut Bencher) {
    b.iter(|| {
        let mut tree = Tree::new();
        let keys = ["/0","/1","/2","/3","/4","/5","/6","/7","/8","/9"];
        for i in 0..10 {
            tree = tree.create(keys[i], NodeType::Blob).unwrap();
        }
    });
}

#[bench]
fn delete_1_node_from_tree_with_10_nodes_at_level_1(b: &mut Bencher) {
    let mut tree = Tree::new();
    let keys = ["/0","/1","/2","/3","/4","/5","/6","/7","/8","/9"];
    for i in 0..10 {
        tree = tree.create(keys[i], NodeType::Blob).unwrap();
    }
    b.iter(|| tree.delete("/5").unwrap())
}
