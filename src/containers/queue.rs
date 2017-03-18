use std::collections::VecDeque;

#[derive(Clone, Debug, Eq, PartialEq,Default)]
pub struct Queue {
    pub data: VecDeque<Vec<u8>>
}

impl Queue {
    pub fn new() -> Queue {
        Queue { data: VecDeque::new() }
    }

    pub fn with_capacity(size: usize) -> Queue {
        Queue { data: VecDeque::with_capacity(size) }
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
        self.data.back()
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn trivial_q() {
        let mut q1 = Queue::new();
        let blob1 = String::from("val1").into_bytes();
        let blob2 = String::from("val2").into_bytes();
        q1.push(blob1.clone());
        q1.push(blob2);
        let res1 = q1.pop();
        match res1 {
            Some(r1) => assert_eq!(r1, blob1),
            None => panic!("got None, expected Some for res1"),
        }
    }
}
