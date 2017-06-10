use node::NodeType;
use rmp_serde;

error_chain! {
    foreign_links {
        Io(::std::io::Error) #[cfg(unix)];
        MsgPackEncodeError(rmp_serde::encode::Error);
        MsgPackDecodeError(rmp_serde::decode::Error);
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
        CasFailed {path: String, expected: u64, actual: u64} {
            description("CAS failed")
            display("CAS failed for {}: Expected {}, Actual {}", path, expected, actual)
        }
        BadPath(msg: String) {
            description("path improperly formatted: must contain a leading slash and at least one
                         component")
            display("path improperly formatted: '{}'", msg)
        }
        CannotDeleteRoot {
            description("Cannot delete root of tree")
            display("Cannot delete root of tree")
        }
        PathMustBeAbsolute(path: String) {
            description("Path must be absolute")
            display("Path must be absolute: '{}'", path)
        }
    }
}
