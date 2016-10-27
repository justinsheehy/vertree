use std::collections::HashSet;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Set {
    pub data: HashSet<Vec<u8>>
}

impl Set {
    pub fn new() -> Set {
        Set {
            data: HashSet::new()
        }
    }

    /// Insert an element into the set.
    /// Returns `true` if the element was added, and `false` if it already existed in the set.
    pub fn insert(&mut self, element: Vec<u8>) -> bool {
        self.data.insert(element)
    }

    /// Remove the element from the set
    /// Returns `true` if the value was present in the set, `false` otherwise
    pub fn remove(&mut self, element: &Vec<u8>) -> bool {
        self.data.remove(element)
    }

    /// Returns `true` if the element is in the set
    pub fn contains(&mut self, element: &Vec<u8>) -> bool {
        self.data.contains(element)
    }

    /// Returns the union of two sets
    ///
    /// # Examples
    ///
    /// ```
    /// use vertree::containers::Set;
    ///
    /// let a = Set { data: [vec![1], vec![2], vec![3]].iter().cloned().collect() };
    /// let b = Set { data: [vec![2], vec![3], vec![4]].iter().cloned().collect() };
    /// assert_eq!(a.union(&b),
    ///            Set { data: [vec![1], vec![2], vec![3], vec![4]].iter().cloned().collect() });
    pub fn union(&self, other: &Set) -> Set {
        Set {
            data: self.data.union(&other.data).cloned().collect()
        }
    }

    /// Returns the intersection of two sets
    ///
    /// # Examples
    ///
    /// ```
    /// use vertree::containers::Set;
    ///
    /// let a = Set { data: [vec![1], vec![2], vec![3]].iter().cloned().collect() };
    /// let b = Set { data: [vec![2], vec![3], vec![4]].iter().cloned().collect() };
    /// assert_eq!(a.intersection(&b),
    ///            Set { data: [vec![2], vec![3]].iter().cloned().collect() });
    pub fn intersection(&self, other: &Set) -> Set {
        Set {
            data: self.data.intersection(&other.data).cloned().collect()
        }
    }

    /// Returns the difference between two sets
    ///
    /// The difference is seen as `self - other`, which is all the keys in `self` that don't exist
    /// in `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vertree::containers::Set;
    ///
    /// let a = Set { data: [vec![1], vec![2], vec![3]].iter().cloned().collect() };
    /// let b = Set { data: [vec![2], vec![3], vec![4]].iter().cloned().collect() };
    /// assert_eq!(a.difference(&b), Set { data: [vec![1]].iter().cloned().collect() });
    pub fn difference(&self, other: &Set) -> Set {
        Set {
            data: self.data.difference(&other.data).cloned().collect()
        }
    }

    /// Returns the symmetric difference between two sets
    ///
    /// The difference is seen as the union of `self - other`, and `other - self`, which is all the
    /// keys that don't exist in both sets.
    ///
    /// # Examples
    ///
    /// ```
    /// use vertree::containers::Set;
    ///
    /// let a = Set { data: [vec![1], vec![2], vec![3]].iter().cloned().collect() };
    /// let b = Set { data: [vec![2], vec![3], vec![4]].iter().cloned().collect() };
    /// assert_eq!(a.symmetric_difference(&b), b.symmetric_difference(&a));
    /// assert_eq!(a.symmetric_difference(&b),
    ///            Set { data: [vec![1], vec![4]].iter().cloned().collect() });
    pub fn symmetric_difference(&self, other: &Set) -> Set {
        Set {
            data: self.data.symmetric_difference(&other.data).cloned().collect()
        }
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
        val: Vec<u8>
    },
    Remove {
        path: String,
        val: Vec<u8>
    },
    Contains {
        path: String,
        val: Vec<u8>
    },
    /// Union of all the sets in the nodes at `paths` and any sets passed in `sets`
    Union {
        paths: Vec<String>,
        sets: Vec<HashSet<Vec<u8>>>
    },
    /// Intersection all the sets in the nodes at `paths` and any sets passed in `sets`
    Intersection {
        paths: Vec<String>,
        sets: Vec<HashSet<Vec<u8>>>
    },
    /// Successively call set.difference on each path in `paths` followed by each set in `sets`
    Difference {
        paths: Vec<String>,
        sets: Vec<HashSet<Vec<u8>>>
    },
    /// Successively call set.symmetric_difference on each path in `paths`
    /// followed by each set in `sets`
    SymmetricDifference {
        paths: Vec<String>,
        sets: Vec<HashSet<Vec<u8>>>
    },
    /// Check to see if the set at `path1` is a subset of the set at `path2` or alternately a subset
    /// of the set passed in `set`. It is an error to have `Some()` variants for both `path2` and
    /// `set`.
    Subset {
        path1: String,
        path2: Option<String>,
        set: Option<HashSet<Vec<u8>>>
    },
    /// Check to see if the set at `path1` is a subset of the set at `path2` or alternately a subset
    /// of the set passed in `set`. It is an error to have `Some()` variants for both `path2` and
    /// `set`.
    Superset {
        path1: String,
        path2: Option<String>,
        set: Option<HashSet<Vec<u8>>>
    }
}
