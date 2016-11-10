#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct Blob {
    pub data: Vec<u8>
}

impl Blob {
    pub fn new() -> Blob {
        Blob {
            data: vec![]
        }
    }

    pub fn fill(data: Vec<u8>) -> Blob {
        Blob {
            data: data
        }
    }

    pub fn put(&mut self, data: Vec<u8>) {
        self.data = data;
    }

    pub fn get(&self) -> &Vec<u8> {
        &self.data
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }
}

/// Operations on Blobs
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum BlobOp {
    Put {
        path: String,
        val: Vec<u8>
    },
    Get {
        path: String
    },
    Len {
        path: String
    }
}

impl BlobOp {
    pub fn is_write(&self) -> bool {
        if let BlobOp::Put {..} = *self {
            return true;
        }
        false
    }
}
