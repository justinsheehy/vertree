use std::collections::VecDeque;
use super::Blob;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Queue {
    data: VecDeque<Blob>
}

impl Queue {
    pub fn new() -> Queue {
        Queue {
            data: VecDeque::new()
        }
    }

    /// Append an element onto the back of the queue
    pub fn push(&mut self, element: Blob) {
        self.data.push_back(element);
    }

    /// Remove the element at the front of the queue and return it
    /// Returns `None` if empty
    pub fn pop(&mut self) -> Option<Blob> {
        self.data.pop_front()
    }

    /// Return a reference to the element at the front of the queue
    /// Returns `None` if empty
    pub fn front(&self) -> Option<&Blob> {
        self.data.front()
    }

    /// Return a reference to the element at the back of the queue
    /// Returns `None` if empty
    pub fn back(&self) -> Option<&Blob> {
        self.data.front()
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }
}

/// Operations on Queues
#[derive(Clone, Debug)]
pub enum QueueOp {
    Push {
        path: String,
        val: Blob
    },
    Pop {
        path: String
    },
    Front {
        path: String
    },
    Back {
        path: String
    },
    Len {
        path: String
    }
}

impl QueueOp {
    /// Returns true if the operation requires updating the tree
    pub fn is_write(&self) -> bool {
        match *self {
            QueueOp::Push {..} => true,
            QueueOp::Pop {..} => true,
            _ => false
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use containers::{Blob};
    #[test]
    fn trivial_q() {
        let mut q1 = Queue::new();
        let val1 = String::from("val1").into_bytes();
        let blob1 = Blob::fill(val1.clone());
        let val2 = String::from("val2").into_bytes();
        let blob2 = Blob::fill(val2.clone());
        q1.push(blob1);
        q1.push(blob2);
        let res1 = q1.pop();
        match res1 {
            Some(ref r1) => assert_eq!(*(r1.get()), val1),
            None => panic!("got None, expected Some for res1")
        }
    }
}

