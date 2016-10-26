use std::collections::{VecDeque, HashSet};

/// The type of a leaf node that holds data
#[derive(Clone, Debug)]
pub enum Container {
    Blob(Blob),
    Queue(Queue),
    Set(Set)
}

#[derive(Clone, Debug)]
pub struct Blob {
    data: Vec<u8>
}

impl Blob {
    pub fn new() -> Blob {
        Blob {
            data: vec![]
        }
    }

    pub fn put(&mut self, data: Vec<u8>) {
        self.data = data;
    }

    pub fn get(&mut self) -> &Vec<u8> {
        &self.data
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }
}

#[derive(Clone, Debug)]
pub struct Queue {
    data: VecDeque<Vec<u8>>
}

impl Queue {
    pub fn new() -> Queue {
        Queue {
            data: VecDeque::new()
        }
    }

    /// Append an element onto the back of the queue
    pub fn push(&mut self, element: Vec<u8>) {
        self.data.push_back(element);
    }

    /// Remove the element at the front of the queue and return it
    /// Returns `None` if empty
    pub fn pop(&mut self) -> Option<Vec<u8>> {
        self.data.pop_front()
    }

    /// Return a reference to the element at the front of the queue
    /// Returns `None` if empty
    pub fn front(&self) -> Option<&Vec<u8>> {
        self.data.front()
    }

    /// Return a reference to the element at the back of the queue
    /// Returns `None` if empty
    pub fn back(&self) -> Option<&Vec<u8>> {
        self.data.front()
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }
}

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
    /// use vertree::container::Set;
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
    /// use vertree::container::Set;
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
    /// use vertree::container::Set;
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
    /// use vertree::container::Set;
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
