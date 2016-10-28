use std::collections::VecDeque;
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

/// Operations on Queues
#[derive(Clone, Debug)]
pub enum QueueOp {
    Push {
        path: String,
        val: Vec<u8>
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

