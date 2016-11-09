use std::collections::HashSet;
use super::Blob;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Set {
    pub data: HashSet<Blob>
}

/// An abstract set datatype
///
/// In order to avoid unnecessary copying, this implementation uses [impl
/// Trait](https://aturon.github.io/blog/2015/09/28/impl-trait/). Currently `impl Trait` is only
/// availible in nightly builds. Here's the implementation
/// [commit](https://github.com/rust-lang/rust/pull/35091).
impl Set {
    pub fn new() -> Set {
        Set {
            data: HashSet::new()
        }
    }

    pub fn with_capacity(size: usize) -> Set {
        Set {
            data: HashSet::with_capacity(size)
        }
    }

    pub fn fill(data: HashSet<Blob>) -> Set {
        Set {
            data: data
        }
    }

    /// Insert an element into the set.
    /// Returns `true` if the element was added, and `false` if it already existed in the set.
    pub fn insert(&mut self, element: Blob) -> bool {
        self.data.insert(element)
    }

    /// Remove the element from the set
    /// Returns `true` if the value was present in the set, `false` otherwise
    pub fn remove(&mut self, element: &Blob) -> bool {
        self.data.remove(element)
    }

    /// Returns `true` if the element is in the set
    pub fn contains(&self, element: &Blob) -> bool {
        self.data.contains(element)
    }

    /// Returns the union of two sets
    ///
    /// # Examples
    ///
    /// ```
    /// use vertree::containers::{Set, Blob};
    ///
    /// let a = Set { data: [Blob::fill(vec![1]),
    ///                      Blob::fill(vec![2]),
    ///                      Blob::fill(vec![3])].iter().cloned().collect() };
    /// let b = Set { data: [Blob::fill(vec![2]),
    ///                      Blob::fill(vec![3]),
    ///                      Blob::fill(vec![4])].iter().cloned().collect() };
    ///
    /// assert_eq!(Set { data: a.union(&b).cloned().collect() },
    ///            Set { data: [Blob::fill(vec![1]),
    ///                         Blob::fill(vec![2]),
    ///                         Blob::fill(vec![3]),
    ///                         Blob::fill(vec![4])].iter().cloned().collect() });
    pub fn union<'a>(&'a self, other: &'a Set) -> impl Iterator<Item=&'a Blob> {
        self.data.union(&other.data)
    }

    /// Returns the intersection of two sets
    ///
    /// # Examples
    ///
    /// ```
    /// use vertree::containers::{Set, Blob};
    ///
    /// let a = Set { data: [vec![1], vec![2], vec![3]].iter().cloned().map(|b| Blob::fill(b)).collect() };
    /// let b = Set { data: [vec![2], vec![3], vec![4]].iter().cloned().map(|b| Blob::fill(b)).collect() };
    ///
    /// let result = Set { data: a.intersection(&b).cloned().collect() };
    /// assert_eq!(result, Set { data: [vec![2], vec![3]].iter().cloned().map(|b| Blob::fill(b)).collect() });
    pub fn intersection<'a>(&'a self, other: &'a Set) -> impl Iterator<Item=&'a Blob> {
        self.data.intersection(&other.data)
    }

    /// Returns the difference between two sets
    ///
    /// The difference is seen as `self - other`, which is all the keys in `self` that don't exist
    /// in `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vertree::containers::{Set, Blob};
    ///
    /// let a = Set { data: [vec![1], vec![2], vec![3]].iter().cloned().map(|b| Blob::fill(b)).collect() };
    /// let b = Set { data: [vec![2], vec![3], vec![4]].iter().cloned().map(|b| Blob::fill(b)).collect() };
    ///
    /// let result = Set { data: a.difference(&b).cloned().collect() };
    /// assert_eq!(result, Set { data: [vec![1]].iter().cloned().map(|b| Blob::fill(b)).collect() });
    pub fn difference<'a>(&'a self, other: &'a Set) -> impl Iterator<Item=&'a Blob> {
        self.data.difference(&other.data)
    }

    /// Returns the symmetric difference between two sets
    ///
    /// The difference is seen as the union of `self - other`, and `other - self`, which is all the
    /// keys that don't exist in both sets.
    ///
    /// # Examples
    ///
    /// ```
    /// use vertree::containers::{Set, Blob};
    ///
    /// let a = Set { data: [vec![1], vec![2], vec![3]].iter().cloned().map(|b| Blob::fill(b)).collect() };
    /// let b = Set { data: [vec![2], vec![3], vec![4]].iter().cloned().map(|b| Blob::fill(b)).collect() };
    ///
    /// let result_a = Set { data: a.symmetric_difference(&b).cloned().collect() };
    /// let result_b = Set { data: b.symmetric_difference(&a).cloned().collect() };
    /// assert_eq!(result_a, result_b);
    /// assert_eq!(result_a,
    ///            Set { data: [vec![1], vec![4]].iter().cloned().map(|b| Blob::fill(b)).collect() });
    pub fn symmetric_difference<'a>(&'a self, other: &'a Set) -> impl Iterator<Item=&'a Blob> {
        self.data.symmetric_difference(&other.data)
    }

    /// Returns `true` if `self` is a subset of `other`
    pub fn is_subset(&self, other: &Set) -> bool {
        self.data.is_subset(&other.data)
    }

    /// Returns `true` if `self` is a subset of `other`
    pub fn is_superset(&self, other: &Set) -> bool {
        self.data.is_superset(&other.data)
    }
}

/// Operations on Sets
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum SetOp {
    Insert {
        path: String,
        val: Blob
    },
    Remove {
        path: String,
        val: Blob
    },
    Contains {
        path: String,
        val: Blob
    },
    /// Union of all the sets in the nodes at `paths` and any sets passed in `sets`
    Union {
        paths: Vec<String>,
        sets: Vec<HashSet<Blob>>
    },
    /// Intersection all the sets in the nodes at `paths` and any sets passed in `sets`
    Intersection {
        paths: Vec<String>,
        sets: Vec<HashSet<Blob>>
    },
    /// Successively call set.difference on each path in `paths` followed by each set in `sets`
    Difference {
        paths: Vec<String>,
        sets: Vec<HashSet<Blob>>
    },
    /// Successively call set.symmetric_difference on each path in `paths`
    /// followed by each set in `sets`
    SymmetricDifference {
        paths: Vec<String>,
        sets: Vec<HashSet<Blob>>
    },
    /// Check to see if the set at `path1` is a subset of the set at `path2` or alternately a subset
    /// of the set passed in `set`. It is an error to have `Some()` variants for both `path2` and
    /// `set`.
    Subset {
        path1: String,
        path2: Option<String>,
        set: Option<HashSet<Blob>>
    },
    /// Check to see if the set at `path1` is a subset of the set at `path2` or alternately a subset
    /// of the set passed in `set`. It is an error to have `Some()` variants for both `path2` and
    /// `set`.
    Superset {
        path1: String,
        path2: Option<String>,
        set: Option<HashSet<Blob>>
    }
}

impl SetOp {
    /// Returns true if the operation requires updating the tree
    pub fn is_write(&self) -> bool {
        match *self {
            SetOp::Insert {..} => true,
            SetOp::Remove {..} => true,
            _ => false
        }
    }
}
