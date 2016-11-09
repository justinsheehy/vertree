use super::NodeType;
use std::io;
use msgpack;

error_chain! {
    foreign_links {
        io::Error, Io;
        msgpack::encode::ValueWriteError, MsgPackValueWriteError;
        msgpack::decode::ValueReadError, MsgPackValueReadError;
    }

    errors {
        AlreadyExists(path: String) {
            description("path already exists")
            display("path already exists: '{}'", path)
        }
        DoesNotExist(path: String) {
            description("path does not exist")
            display("path does not exist: '{}'", path)
        }
        WrongType(path: String, ty: NodeType) {
            description("Node at path is of the wrong type")
            display("Node at path '{}' is of the wrong type: '{:?}'", path, ty)
        }
        InvalidPathContent(path: String) {
            description("path does not end in a directory")
            display("path does not end in a directory: '{}'", path)
        }
        BadPath(msg: String) {
            description("path improperly formatted: must contain a leading slash and at least one
                         component")
            display("path improperly formatted: '{}'", msg)
        }
    }
}
