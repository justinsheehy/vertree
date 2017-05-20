use std::collections::hash_map::RandomState;
use std::collections::hash_set::{self, HashSet};
use std::fmt;

#[derive(Clone, Debug, Eq, PartialEq,Default)]
pub struct Set {
    pub data: HashSet<Vec<u8>>
}

/// An abstract set datatype
impl Set {
    pub fn new() -> Set {
        Set { data: HashSet::new() }
    }

    pub fn with_capacity(size: usize) -> Set {
        Set { data: HashSet::with_capacity(size) }
    }

    pub fn fill(data: HashSet<Vec<u8>>) -> Set {
        Set { data: data }
    }

    /// Insert an element into the set.
    /// Returns `true` if the element was added, and `false` if it already
    /// existed in the set.
    pub fn insert(&mut self, element: Vec<u8>) -> bool {
        self.data.insert(element)
    }

    /// Remove the element from the set
    /// Returns `true` if the value was present in the set, `false` otherwise
    pub fn remove(&mut self, element: &[u8]) -> bool {
        self.data.remove(element)
    }

    /// Returns `true` if the element is in the set
    pub fn contains(&self, element: &[u8]) -> bool {
        self.data.contains(element)
    }

    /// Returns the number of elements in the Set
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Returns `true` if the `Set` is empty
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }


    /// Returns the union of two sets
    ///
    /// # Examples
    ///
    /// ```
    /// use vertree::containers::Set;
    ///
    /// let a = Set { data: vec![vec![1],
    ///                          vec![2],
    ///                          vec![3]].into_iter().collect() };
    /// let b = Set { data: vec![vec![1],
    ///                          vec![2],
    ///                          vec![3],
    ///                          vec![4]].into_iter().collect() };
    ///
    /// assert_eq!(Set { data: a.union(&b).cloned().collect() },
    ///            Set { data: vec![vec![1],
    ///                             vec![2],
    ///                             vec![3],
    ///                             vec![4]].into_iter()
    ///                                     .collect() });
    pub fn union<'a>(&'a self, other: &'a Set) -> Union<'a> {
        Union {
            iter: self.data.union(&other.data),
        }
    }

    /// Returns the intersection of two sets
    ///
    /// # Examples
    ///
    /// ```
    /// use vertree::containers::Set;
    ///
    /// let a = Set { data: vec![vec![1],
    ///                          vec![2],
    ///                          vec![3]].into_iter().collect() };
    /// let b = Set { data: vec![vec![2],
    ///                          vec![3],
    ///                          vec![4]].into_iter().collect() };
    ///
    /// let result = Set { data: a.intersection(&b).cloned().collect() };
    /// assert_eq!(result, Set { data: vec![vec![2],
    ///                                     vec![3]].into_iter().collect() });
    pub fn intersection<'a>(&'a self, other: &'a Set) -> Intersection<'a> {
        Intersection {
            iter: self.data.intersection(&other.data),
        }
    }

    /// Returns the difference between two sets
    ///
    /// The difference is seen as `self - other`, which is all the keys in
    /// `self` that don't exist
    /// in `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use vertree::containers::Set;
    ///
    /// let a = Set { data: vec![vec![1],
    ///                          vec![2],
    ///                          vec![3]].into_iter().collect() };
    /// let b = Set { data: vec![vec![2],
    ///                          vec![3],
    ///                          vec![4]].into_iter().collect() };
    ///
    /// let result = Set { data: a.difference(&b).cloned().collect() };
    /// assert_eq!(result, Set { data: vec![vec![1]].into_iter().collect() });
    pub fn difference<'a>(&'a self, other: &'a Set) -> Difference<'a> {
        Difference {
            iter: self.data.difference(&other.data),
        }
    }

    /// Returns the symmetric difference between two sets
    ///
    /// The difference is seen as the union of `self - other`, and `other -
    /// self`, which is all the
    /// keys that don't exist in both sets.
    ///
    /// # Examples
    ///
    /// ```
    /// use vertree::containers::Set;
    ///
    /// let a = Set { data: vec![vec![1],
    ///                          vec![2],
    ///                          vec![3]].into_iter().collect() };
    /// let b = Set { data: vec![vec![2],
    ///                          vec![3],
    ///                          vec![4]].into_iter().collect() };
    ///
    /// let result_a = Set { data: a.symmetric_difference(&b)
    ///                             .cloned()
    ///                             .collect() };
    /// let result_b = Set { data: b.symmetric_difference(&a)
    ///                             .cloned()
    ///                             .collect() };
    /// assert_eq!(result_a, result_b);
    /// assert_eq!(result_a,
    ///            Set { data: vec![vec![1], vec![4]].into_iter().collect() });
    pub fn symmetric_difference<'a>(&'a self, other: &'a Set) -> SymmetricDifference<'a> {
        SymmetricDifference {
            iter: self.data.symmetric_difference(&other.data),
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

/// A lazy iterator producing elements in the union of `Set`s.
///
/// This `struct` is created by the [`union`] method on
/// [`Set`]. See its documentation for more.
///
/// [`Set`]: struct.Set.html
/// [`union`]: struct.Set.html#method.union
#[derive(Clone)]
pub struct Union<'a> {
    iter: hash_set::Union<'a, Vec<u8>, RandomState>,
}

impl<'a> fmt::Debug for Union<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.iter.fmt(f)
    }
}

impl<'a> Iterator for Union<'a> {
    type Item = &'a Vec<u8>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

/// A lazy iterator producing elements in the intersection of `Set`s.
///
/// This `struct` is created by the [`intersection`] method on
/// [`Set`]. See its documentation for more.
///
/// [`Set`]: struct.Set.html
/// [`intersection`]: struct.Set.html#method.intersection
#[derive(Clone)]
pub struct Intersection<'a> {
    iter: hash_set::Intersection<'a, Vec<u8>, RandomState>,
}

impl<'a> fmt::Debug for Intersection<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.iter.fmt(f)
    }
}

impl<'a> Iterator for Intersection<'a> {
    type Item = &'a Vec<u8>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

/// A lazy iterator producing elements in the difference of `Set`s.
///
/// This `struct` is created by the [`difference`] method on
/// [`Set`]. See its documentation for more.
///
/// [`Set`]: struct.Set.html
/// [`difference`]: struct.Set.html#method.difference
#[derive(Clone)]
pub struct Difference<'a> {
    iter: hash_set::Difference<'a, Vec<u8>, RandomState>,
}

impl<'a> fmt::Debug for Difference<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.iter.fmt(f)
    }
}

impl<'a> Iterator for Difference<'a> {
    type Item = &'a Vec<u8>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

/// A lazy iterator producing elements in the symmetric difference of `Set`s.
///
/// This `struct` is created by the [`symmetric_difference`] method on
/// [`Set`]. See its documentation for more.
///
/// [`Set`]: struct.Set.html
/// [`symmetric_difference`]: struct.Set.html#method.symmetric_difference
#[derive(Clone)]
pub struct SymmetricDifference<'a> {
    iter: hash_set::SymmetricDifference<'a, Vec<u8>, RandomState>,
}

impl<'a> fmt::Debug for SymmetricDifference<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.iter.fmt(f)
    }
}

impl<'a> Iterator for SymmetricDifference<'a> {
    type Item = &'a Vec<u8>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}
