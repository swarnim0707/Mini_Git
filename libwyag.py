import argparse, configparser
from datetime import datetime
import grp, pwd
from fnmatch import fnmatch
import hashlib
from math import ceil
import os, re, sys, zlib
# from constants import Commands
import struct
import shutil

argparser = argparse.ArgumentParser(description="Version-Control Command Parser")
argsubparsers = argparser.add_subparsers(title = "Commands", dest = "command")
argsubparsers.required = True

argsubparsers.add_parser("init",
                         help="Initialize a new, empty repository.").\
                         add_argument("path",
                                    metavar="directory",
                                    nargs = "?",
                                    default = ".",
                                    help = "Where to create the repository"
                                )

argsp = argsubparsers.add_parser("cat-file",
                                 help="Provide content of repository objects")

argsp.add_argument("type",
                   metavar="type",
                   choices=["blob", "commit", "tag", "tree"],
                   help="Specify the type")

argsp.add_argument("object",
                   metavar="object",
                   help="The object to display")

def main(argv = sys.argv[1:]):
    args = argparser.parse_args(argv)
    match args.command:
        case "cat-file"     : cmd_cat_file(args)
        case "check-ignore" : cmd_check_ignore(args)
        case "checkout"     : cmd_checkout(args)
        case "commit"       : cmd_commit(args)
        case "hash-object"  : cmd_hash_object(args)
        case "init"         : cmd_init(args)
        case "log"          : cmd_log(args)
        case "ls-files"     : cmd_ls_files(args)
        case "ls-tree"      : cmd_ls_tree(args)
        case "rev-parse"    : cmd_rev_parse(args)
        case "rm"           : cmd_rm(args)
        case "show-ref"     : cmd_show_ref(args)
        case "status"       : cmd_status(args)
        case "tag"          : cmd_tag(args)
        case _              : print("Bad command.")

def cmd_init(args):
    repo_create(args.path)

def repo_path(repo, *path):
    """Compute path under the repository's gitdir directory"""
    return os.path.join(repo.gitdir, *path)

def repo_file(repo, *path, mkdir = False):
    """
    Compute path under the gitdir directory; if absent, create dirname(*path)
    up until before the last component using repo_dir
    """
    if(repo_dir(repo, *path[:-1], mkdir = mkdir)):
        return repo_path(repo, *path)
    return None # If the condition is not satisfied
    
def repo_dir(repo, *path, mkdir):
    """
    Same as repo_path, but mkdir *path if absent if mkdir
    Also checks if the given dir path already exists but is not a directory
    """

    path = repo_path(repo, *path)

    if(os.path.exists(path)):
        if(os.path.isdir(path)):
            return path
        else:
            raise Exception(f"{path} already exists but it is not a directory")
    
    if mkdir:
        return os.makedirs(path)
    else:
        return None
    
def repo_create(path):
    """Create a new repository at the given path"""

    repo = GitRepository(path, force = True)

    # We ensure the path either doesn't exist or is an empty dir

    if(os.path.exists(repo.worktree)):
        if not os.path.isdir(repo.worktree):
            raise Exception(f"{path} exists and is not a directory")
        if os.path.exists(repo.gitdir) and os.listdir(repo.gitdir):
            raise Exception(f"{path} is already a git repo!")
    else:
        os.makedirs(repo.worktree)

    assert repo_dir(repo, "branches", mkdir=True)
    assert repo_dir(repo, "objects", mkdir=True)
    assert repo_dir(repo, "refs", "tags", mkdir=True)
    assert repo_dir(repo, "refs", "heads", mkdir=True)

    # Creating .git/description
    with open(repo_file(repo, "description"), 'w') as description:
        description.write("Unnamed repository; edit this file 'description' to name the repository.\n")

    # Creating .git/HEAD
    with open(repo_file(repo, "HEAD"), 'w') as head:
        head.write("ref: refs/heads/master\n")

    with open(repo_file(repo, "config"), "w") as f:
        config = repo_default_config()
        config.write(f)

def repo_default_config():
    config = configparser.ConfigParser()

    config.add_section("core")
    config.set("core", "repositoryformatversion", "0")
    config.set("core", "filemode", "false")
    config.set("core", "bare", "false")

    return config

def repo_find(path = ".", required = True):
    """
    Recursively finds the worktree, i.e. the folder which contains the .git directory
    and returns the GitRepository object of that folder's path. In case of no worktree
    found, raises an Exception. 
    """
    path = os.path.realpath(path)

    if(os.path.exists(os.path.join(path, ".git"))):
        if(os.path.isdir(os.path.join(path, ".git"))):
            return GitRepository(path)
        
    parent = os.path.join(path, "..")

    if(parent == path):
        if required:
            raise Exception(f"{path} is the root folder and it is not a repository")
        else:
            return None
    
    return repo_find(parent, required)

def object_read(repo, sha, return_type = False):
    """
    Read object sha from Git repository repo. Returns a
    GitObject whose exact type depends on the object and
    contains deserialized data.
    """

    file_path = repo_file(repo, "objects", sha[:2], sha[2:])

    if not os.path.isfile(file_path):
        return None
    
    with open (file_path, "rb") as f:
        raw = zlib.decompress(f.read())

        # Read object type
        x = raw.find(b' ')
        fmt = raw[0:x]

        # Read and validate object size
        y = raw.find(b'\x00', x)
        size = int(raw[x+1:y].decode("ascii"))
        if size != len(raw)-y-1:
            raise Exception(f"Malformed object {sha}: bad length")

        if return_type:
            return fmt

        # Pick constructor
        match fmt:
            case b'commit' : c=GitCommit
            case b'tree'   : c=GitTree
            case b'tag'    : c=GitTag
            case b'blob'   : c=GitBlob
            case _:
                raise Exception(f"Unknown type {fmt.decode("ascii")} for object {sha}")

        # Call constructor and return object
        return c(raw[y+1:])
    
def object_write(obj, repo = None):

    # Serialize object data
    data = obj.serialize()
    # Add header
    data = obj.fmt + str(len(data)).encode() + b'\x00' + data
    # Compute the hash value of the object
    sha = hashlib.sha1(data).hexdigest()

    if repo:
        # Compute path
        path = repo_file(repo, "objects", sha[:2], sha[2:], mkdir = True)

        if not os.path.exists(path):
            with open(path, 'wb') as file:
                file.write(zlib.compress(sha))

    return sha


class GitRepository(object):
    """Creates a Git Rep                                                                                                                                                                                                                                                    ository object"""

    gitdir = conf = worktree = None

    def __init__(self, path, force = False):
        self.worktree = path
        self.gitdir = os.path.join(".git")

        if not (force or os.path.isdir(self.gitdir)):
            raise Exception(f"{path} is not a valid git repository")
        
        # Read config file in the .git/config
        self.config = configparser.ConfigParser()
        cf = repo_file(self, "config")

        if(cf and os.path.exists(cf)):
            self.config.read([cf])
        elif not force:
            raise Exception("Configuration file missing")
        
        if(not force):
            version = int(self.config.get("core", "repositoryFormatVersion"))
            if version:
                raise Exception(f"Unsupported repositoryFormatVersion: {version}")
            
class GitObject(object):

    def __init__(self, data = None):
        """During initialization the deserialization function is called"""
        if data != None:
            self.deserialize(data)
        else:
            self.init()

    def deserialize(self, data):
        raise Exception("Needs to be implemented by subclass")
    
    def serialize(self, repo):
        """
        It must read the object's contents from self.data, a byte string, and
        do whatever it takes to convert it into a meaningful representation.
        What exactly that means depend on each subclass.
        """
        raise Exception("Needs to be implemented by subclass")
    
class GitBlob(GitObject):
    fmt=b'blob'

    def serialize(self):
        return self.blobdata

    def deserialize(self, data):
        self.blobdata = data


# cat-file command: Shows raw contents of an object, uncompressed and without the header

argsp = argsubparsers.add_parser("cat-file", help = "Provide content of repository objects")
argsp.add_argument("type", metavar = "type", choices = ["blob", "commit", "tag", "tree"], help = "Specify the type")
argsp.add_argument("object", metavar = "Object", help = "The object to display")

def cmd_cat_file(args):
    repo = repo_find()
    cat_file(repo, args.object, fmt = args.type.encode())

def cat_file(repo, obj, fmt = None):
    obj = object_read(repo, object_find(repo, obj, fmt = fmt))
    sys.stdout.buffer.write(obj.serialize())

def object_find(repo, name, fmt = None, follow = True):
    return name

# Hash-object command

argsp = argsubparsers.add_parser("hash-object", help = "Compute obj ID and optionally create a blob from a file")
argsp.add_argument("-t", dest = "type", metavar = "type", choices = ["blob", "commit", "tree", "tag"], default = "blob",
                    help = "Specify the type")
argsp.add_argument("-w", dest = "write", metavar = "write", action = "store_true",
                    help = "Actually write the object into the database")

argsp.add_argument("path",
                   help="Read object from <file>")

def cmd_hash_object(args):
    if args.write:
        repo = repo_find()
    else:
        repo = None

    sha = hash_object(args, args.type.encode(), repo)
    print(sha)

def hash_object(path, fmt, repo = None):
    with open(path, 'rb') as file:
        data = file.read()

    match fmt:
        case b'commit'  :    obj=GitCommit(data)
        case b'tree'    :    obj=GitTree(data)
        case b'tag'     :    obj=GitTag(data)
        case b'blob'    :    obj=GitBlob(data)
        case _: raise Exception(f"Unknown type {fmt}!")

    sha = object_write(obj, repo)
    return sha

# Parsing commit objects

def kvlm_deserialize(raw, start = 0, dct = None):
    """
    Takes binary-encoded data of the commit object as input.
    Recursive function: Keeps calling itself till it reaches the end of the object
    Reads key-value pairs
    """

    if not dct:
        dct = dict()

    space_index = raw.find(b' ', start)
    newline_index = raw.find(b'\n', start)

    # Base case: New-line appears before the space or there is not space at all which implies a blank line
    # A blank line means rest of the data is the message

    if space_index == -1 or newline_index < space_index:
        assert newline_index == start
        dct[None] = raw[newline_index + 1:]
        return dct

    # New-line followed by a space is a continuation of the value in the previous line and not the beginning of a new key-value pair
    key = raw[start:space_index]
    while (raw[newline_index+1] == b' '):
        newline_index = raw.find(b'\n', newline_index)
    
    value = raw[space_index+1:newline_index].replace(b'\n ', b'\n')

    # If the key already exists in the dict, don't replace its value with the new one
    # Append it to the list of values

    if key in dct.keys():
        if type(dct[key] == list):
            dct[key].append(value)
        else:
            dct[key] = [dct[key], value]
    else:
        dct[key] = value

    return kvlm_deserialize(raw, newline_index+1, dct)

    
def kvlm_serialize(dct):

    serialized_data = b''

    for k in dct.keys():
        if k == None: continue

        val = dct[k]
        if type(val) != list:
            val = list(val)

        for value in val:
            serialized_data += k + b' ' + value.replace(b'\n', b'\n ') + b'\n'

    serialized_data += b'\n' + dct[None]

    return serialized_data

# Commit Object

class GitCommit(GitObject):
    fmt = b'commit'

    def deserialize(self, data):
        self.kvlm = kvlm_deserialize(data)

    def serialize(self):
        return kvlm_serialize(self.kvlm)

    def init(self):
        self.kvlm = dict()


# The log command

argsp = argsubparsers.add_parser('log', metavar = 'log', help = "Display history of a given commit")
argsp.add_argument("commit", default = "HEAD", nargs = "?", help = "Commit to start at")

def cmd_log(args):
    repo = repo_find()
    print("digraph wyaglog{")
    print("  node[shape=rect]")
    log_graphviz(repo, object_find(repo, args.commit), set())
    print("}")

def log_graphviz(repo, sha, seen):
    if sha in seen:
        return
    seen.add(sha)

    commit = object_read(repo, sha)
    message = commit.kvlm[None].decode('utf8').strip()
    message = message.replace("\\", "\\\\")
    message = message.replace("\"", "\\\"")

    if "\n" in message: # Keep only the first line
        message = message[:message.index("\n")]

    print(f"  c_{sha} [label=\"{sha[0:7]}: {message}\"]")
    assert commit.fmt==b'commit'

    if not b'parent' in commit.kvlm.keys():
        # Base case: Initial commit with no parent
        return

    parents = commit.kvlm[b'parent']

    if type(parents) != list:
        parents = [ parents ]

    for p in parents:
        p = p.decode("ascii")
        print (f"  c_{sha} -> c_{p};")
        log_graphviz(repo, p, seen)

# Handling Tree Objects

class GitTreeLeaf(object):
    def __init__(self, mode, path, sha):
        self.mode = mode
        self.path = path
        self.sha = sha

class GitTree(GitObject):
    fmt=b'tree'

    def deserialize(self, data):
        self.items = tree_deserialize(data)

    def serialize(self):
        return tree_serialize(self.items)

    def init(self):
        self.items = list()

def tree_deserialize(data):
    pos = 0
    max = len(data)
    leaf_list = []

    while(pos < max):
        pos, leaf = tree_leaf_parse(data, pos)
        leaf_list.append(leaf)

    return leaf_list

def tree_leaf_parse(data, pos = 0):

    # mode [space] path [\x00] sha

    # Finding the first space
    space = data.find(b' ', pos)

    mode = data[pos:space]
    if len(mode) == 5:
        mode = b'0' + mode
    
    # Finding the null terminator
    null_terminator = data.find(b'\x00', space)
    path = data[space+1:null_terminator]

    # Read the SHA - It spans for exactly 20 bytes in binary encoding
    raw_sha = int.from_bytes(data[null_terminator+1:null_terminator+21], "big")
    # Convert the SHA into a hex string, padded to 40 chars
    # with zeros if needed
    sha = format(raw_sha, "040x")

    return null_terminator+1, GitTreeLeaf(mode, path.decode("utf8"), sha)

def tree_leaf_sort_key(leaf):
    # Notice this isn't a comparison function, but a conversion function.
    # Python's default sort doesn't accept a custom comparison function,
    # like in most languages, but a `key` arguments that returns a new
    # value, which is compared using the default rules.  So we just return
    # the leaf name, with an extra / if it's a directory.
    if leaf.mode.startswith(b"10"):
        return leaf.path
    else:
        return leaf.path + "/"

def tree_serialize(leaf_list):

    leaf_list.sort(key = tree_leaf_sort_key)
    binary_data = b''
    for leaf in leaf_list:
        binary_data += leaf.mode + b' '
        binary_data += leaf.path.encode('utf8') + b'\x00'
        raw_sha = int(leaf.sha, 16)
        sha_in_bytes = raw_sha.to_bytes(20, byteorder="big")
        binary_data += sha_in_bytes
    return binary_data

# ls-tree command implementation

argsp = argsubparsers.add_parser("ls-tree", help="Pretty-print a tree object.")
argsp.add_argument("-r",
                   dest="recursive",
                   action="store_true",
                   help="Recurse into sub-trees")

argsp.add_argument("tree",
                   help="A tree-ish object.")

def cmd_ls_tree(args):
    repo = repo_find()
    ls_tree(repo, args.tree, args.recursive)

def ls_tree(repo, sha_ref, recursive = None, prefix_path = ''):
    sha = object_find(repo, sha_ref, fmt = b'tree')
    obj = object_read(repo, sha) # Obj contains the deserialized tree data, i.e., the list of leaf objects

    for leaf in obj:
        if len(leaf.mode) == 5:
            type = leaf.mode[0]
        else:
            type = leaf.mode[0:2]

        match type:
            case b'04': type = "tree"
            case b'10': type = "blob" # A regular file
            case b'12': type = "blob" # A symlink
            case b'16': type = "commit" # A submodule
            case _: raise Exception(f"Invalid tree leaf mode {leaf.mode}")

        if not (recursive or type == "tree"):
            # Base case
            print(f"{'0' * (6 - len(leaf.mode)) + leaf.mode.decode('ascii')} {type} {leaf.sha}\t{os.path.join(prefix_path, leaf.path)}")
        else:
            # Recursive case
            ls_tree(repo, leaf.sha, recursive = None, prefix_path = os.path.join(prefix_path, leaf.path))


# Commit command: Strictly implementing only for an empty directory to checkout to

argsp = argsubparsers.add_parser("checkout", help="Checkout a commit inside of a directory.")

# Commit argument takes the reference (usually sha) of the commit or the tree
argsp.add_argument("commit",
                   help="The commit or tree to checkout.")

argsp.add_argument("path",
                   help="The directory to checkout on.") # Needs to be a full path not relative

def cmd_checkout(args):
    repo = repo_find()
    obj = object_read(repo, object_find(repo, args.commit, fmt = b'tree')) # object_find finds the final tree sha
                                                                           # regardless of what sha is provided

    # Now confirm if the provided directory is actually a directory
    if os.path.exists(args.path, mkdir = True):
        if not os.path.isdir(args.path):
            raise Exception(f"Not a directory {args.path}!")
    else:
        os.makedirs(args.path)

    tree_checkout(repo, args.path, obj)

def tree_checkout(repo, dir_path, tree_obj):
    for leaf in tree_obj:
        destination = os.path.join(dir_path, leaf.path)
        obj = object_read(repo, object_find(repo, leaf.sha))

        # Since during the checkout, existing files in the directory will be over-written, we remove them if they already exist
        # We do not empty the directory by default because the files not mentioned in the tree object remain untouched
        if os.path.exists(destination):
            if not os.path.isdir(destination):
                os.remove(destination)
            elif os.path.listdir(destination):
                shutil.rmtree("path/to/directory")
            else:
                os.rmdir(destination)

        # If the mode is of a tree, recursively run the function to parse the tree object and create files
        # If it is not a tree, then create that object in the given path
        if obj.fmt == b'tree':
            os.mkdir(destination)
            tree_checkout(repo, destination, obj)
        elif obj.fmt == b'blob':
            # A symlink is handled the same as a blob

            with open(destination, 'wb') as file:
                file.write(obj.blobdata)
        elif obj.fmt == b'commit':
            os.mkdir(destination)
            append_git_index(repo, leaf.mode, leaf.sha, destination)

def append_git_index(repo, mode, sha, path):
    """
    Creates the binary index file at .git/index
    """

    # Preparing the entry
    index_entry = convert_tree_leaf_to_index_format(mode, sha, path)

    path = repo_file(repo, "index")
    with open(path, 'wb') as file:
        file.write(index_entry)

def convert_tree_leaf_to_index_format(mode_in_binary, sha_hex, path_decoded):
    mode_int = int(mode_in_binary.decode(), 8)  # Convert from octal string to int
    mode_packed = struct.pack(">I", mode_int)  # Convert to 4-byte big-endian format
    sha_in_bytes = bytes.fromhex(sha_hex) # Convert SHA-1 from hex string to raw 20-byte binary format
    path_bytes = path_decoded.encode('utf-8') + b'\x00' # Encode path as a null-terminated string

    index_entry = mode_packed + sha_in_bytes + path_bytes

    return index_entry


# Handling references

argsp = argsubparsers.add_parser("show-ref", help="List references.")

def cmd_show_ref(args):
    repo = repo_find()
    refs = ref_list(repo)
    show_ref(repo, refs, prefix="refs")

def show_ref(repo, refs, with_hash=True, prefix=""):
    for k, v in refs.items():
        if type(v) == str:
            print (f"{' ' if with_hash else ''}{'/' if prefix else ''}{k}")
        else:
            show_ref(repo, v, with_hash=with_hash, prefix=f"{prefix}{'/' if prefix else ''}{k}")

def ref_list(repo, path = None):
    if not path:
        path = repo_dir(repo, "refs")
    ref_dict = dict()
    # Git shows refs sorted. To do the same, we sort the output of listdir
    for item in sorted(os.listdir(path)):
        item_path = os.path.join(path, item)
        if os.path.isdir(item_path):
            ref_dict[item] = ref_list(repo, item_path)
        else:
            ref_dict[item] = ref_resolve(repo, item_path)

    return ref_dict

def ref_resolve(repo, ref):
    path = repo_file(repo, ref)

    if not path: # If ref provided is already the full path and not relative, repo_file will return None
        path = ref

    if not os.path.isfile(path):
        return None # Sometimes, an indirect reference may be broken.

    with open(path, 'r') as fp:
        data = fp.read()[:-1] # Drop final \n

    if data.startswith("ref: "):
        return ref_resolve(repo, data[5:])
    else:
        return data


# Handling tag objects

class GitTag(GitCommit):
    fmt = b'tag'

argsp = argsubparsers.add_parser(
    "tag",
    help="List and create tags")

argsp.add_argument("-a",
                   action="store_true",
                   dest="create_tag_object",
                   help="Whether to create a tag object")

argsp.add_argument("name",
                   nargs="?",
                   help="The new tag's name")

argsp.add_argument("object",
                   default="HEAD",
                   nargs="?",
                   help="The object the new tag will point to")

def cmd_tag(args):
    repo = repo_find()

    if args.name:
        tag_create(repo,
                   args.name,
                   args.object,
                   create_tag_object = args.create_tag_object)
    else:
        refs = ref_list(repo)
        show_ref(repo, refs["tags"], with_hash=False)

def tag_create(repo, tag_name, ref_obj, create_tag_object = False):
    sha = object_find(repo, ref_obj)

    if create_tag_object:
        kvlm = dict()
        kvlm[b'object'] = sha.encode()
        kvlm[b'type'] = object_read(repo, sha, return_type=True)
        kvlm[b'name'] = tag_name.encode()
        kvlm[None] = b"A tag generated by wyag, which won't let you customize the message!\n"
        tag = GitTree(kvlm)
        tag_sha = object_write(tag, repo)
        # create reference
        ref_create(repo, "tags/" + tag_name, tag_sha)
    else:
        # create lightweight tag (ref)
        ref_create(repo, "tags/" + tag_name, sha)

def ref_create(repo, ref_name, ref):
    with open(repo_file(repo, "refs/" + ref_name), 'w') as fp:
        fp.write(ref + "\n") # Because reference files end with a line change

def object_resolve(repo, name):
    """
    Resolve name to an object hash in repo.

    This function is aware of:

        - the HEAD literal
        - short and long hashes
        - tags
        - branches
        - remote branches
    """

    # Empty string will return None
    if not name.strip():
        return None

    # Head is nonambiguous
    if name == "HEAD":
        return [ref_resolve(repo, "HEAD")]

    candidates = list()
    hashRE = re.compile(r"^[0-9A-Fa-f]{4,40}$")

    if hashRE.match(name):
        name = name.lower()
        prefix = name[:2]

        path = repo_dir(repo, "objects", prefix, mkdir = False)
        if path:
            rem_file_name = name[2:]
            for file in os.path.listdir(prefix):
                if file.startswith(rem_file_name):
                    candidates.append(file)

    # If it does not exist as an object, it might be in the references directory
    as_tag = ref_resolve(repo, "refs/tags/" + name)
    if as_tag: # Did we find a tag?
        candidates.append(as_tag)

    as_branch = ref_resolve(repo, "refs/heads/" + name)
    if as_branch: # Did we find a branch?
        candidates.append(as_branch)

    return candidates



def object_find(repo, name, fmt = None, follow = True):
    sha = object_resolve(repo, name)

    if not sha:
        raise Exception(f"No reference to the provided name ({name}) found")

    if len(sha) > 1:
        raise Exception(f"Ambiguous reference {name}: Candidates are:\n - {'\n - '.join(sha)}")

    if not fmt:
        return sha

    while True:
        obj_fmt = object_read(repo, sha, return_type=True)

        if obj_fmt == fmt:
            return object_read(repo, sha)

        if not follow:
            return None

        obj = object_read(repo, sha)

        if obj.fmt == b'tag':
            sha = obj.kvlm[b'object'].decode('ascii')
        elif obj.fmt == b'commit' and fmt == b'tree':
            sha = obj.kvlm[b'tree'].decode('ascii')
        else:
            return None


# Handling the index file

class GitIndexEntry (object):
    def __init__(self, ctime=None, mtime=None, dev=None, ino=None,
                 mode_type=None, mode_perms=None, uid=None, gid=None,
                 fsize=None, sha=None, flag_assume_valid=None,
                 flag_stage=None, name=None):
        # The last time a file's metadata changed.  This is a pair
        # (timestamp in seconds, nanoseconds)
        self.ctime = ctime
        # The last time a file's data changed.  This is a pair
        # (timestamp in seconds, nanoseconds)
        self.mtime = mtime
        # The ID of device containing this file
        self.dev = dev
        # The file's inode number
        self.ino = ino
        # The object type, either b1000 (regular), b1010 (symlink), b1110 (gitlink)
        self.mode_type = mode_type
        # The object permissions, an integer
        self.mode_perms = mode_perms
        # User ID of owner
        self.uid = uid
        # Group ID of owner
        self.gid = gid
        # Size of this object, in bytes
        self.fsize = fsize
        # The object's SHA reference
        self.sha = sha
        self.flag_assume_valid = flag_assume_valid
        self.flag_stage = flag_stage
        # Name of the object with the full path
        self.name = name

class GitIndex (object):
    version = None
    entries = []

    def __init__(self, version=2, entries=None):
        if not entries:
            entries = list()

        self.version = version
        self.entries = entries

def index_parser(repo):
    index_file = repo_file(repo, "index")

    if not os.path.isfile(index_file):
        return GitIndex() # New repositories don't have an index file yet

    with open(index_file, 'rb') as file:
        index_file_content = file.read()

    header = index_file_content[:12]
    signature = header[:4]
    assert signature == b'DIRC' # DIRC stand for directory cache
    version = int.from_bytes(header[4:8], "big")
    assert version == 2, "Our implementation only supports index file version 2"
    # 1: Very old format (obsolete). No longer used.
    # 2: Introduced CRC checks, compact format for file metadata.
    # 3: Adds extended flags for additional file tracking.
    # 4: Uses path compression (delta encoding) for smaller index sizes.
    count = int.from_bytes(header[8:12], "big")

    entries = list()

    content = index_file_content[12:]

    idx = 0
    for i in range(count):
        # Read creation time, as a unix timestamp (seconds since
        # 1970-01-01 00:00:00, the "epoch")
        ctime_s =  int.from_bytes(content[idx: idx+4], "big")
        # Read creation time, as nanoseconds after that timestamps,
        # for extra precision.
        ctime_ns = int.from_bytes(content[idx+4: idx+8], "big")
        # Same for modification time: first seconds from epoch.
        mtime_s = int.from_bytes(content[idx+8: idx+12], "big")
        # Then extra nanoseconds
        mtime_ns = int.from_bytes(content[idx+12: idx+16], "big")
        # Device ID
        dev = int.from_bytes(content[idx+16: idx+20], "big")
        # Inode
        ino = int.from_bytes(content[idx+20: idx+24], "big")
        # Ignored.
        unused = int.from_bytes(content[idx+24: idx+26], "big")
        assert 0 == unused
        mode = int.from_bytes(content[idx+26: idx+28], "big")
        mode_type = mode >> 12
        assert mode_type in [0b1000, 0b1010, 0b1110]
        mode_perms = mode & 0b0000000111111111
        # User ID
        uid = int.from_bytes(content[idx+28: idx+32], "big")
        # Group ID
        gid = int.from_bytes(content[idx+32: idx+36], "big")
        # Size
        fsize = int.from_bytes(content[idx+36: idx+40], "big")
        sha = format(int.from_bytes(content[idx+40: idx+60], "big"), "040x")
        # Flags we're going to ignore
        flags = int.from_bytes(content[idx+60: idx+62], "big")
        # Parse flags
        flag_assume_valid = (flags & 0b1000000000000000) != 0
        flag_extended = (flags & 0b0100000000000000) != 0
        assert not flag_extended
        flag_stage =  flags & 0b0011000000000000
        # Length of the name.  This is stored on 12 bits, some max
        # value is 0xFFF, 4095.  Since names can occasionally go
        # beyond that length, git treats 0xFFF as meaning at least
        # 0xFFF, and looks for the final 0x00 to find the end of the
        # name --- at a small, and probably very rare, performance
        # cost.
        name_length = flags & 0b0000111111111111

        # We've read 62 bytes so far.
        idx += 62

        if name_length < 0xFFF:
            assert content[idx + name_length] == 0x00
            raw_name = content[idx:idx+name_length]
            idx += name_length + 1
        else:
            print(f"Notice: Name is 0x{name_length:X} bytes long.")
            # This probably wasn't tested enough.  It works with a
            # path of exactly 0xFFF bytes.  Any extra bytes broke
            # something between git, my shell and my filesystem.
            null_idx = content.find(b'\x00', idx + 0xFFF)
            raw_name = content[idx: null_idx]
            idx = null_idx + 1

        # Just parse the name as utf8.
        name = raw_name.decode("utf8")

        # Data is padded on multiples of eight bytes for pointer
        # alignment, so we skip as many bytes as we need for the next
        # read to start at the right position.

        idx = 8 * ceil(idx / 8)
        # And we add this entry to our list.
        entries.append(GitIndexEntry(ctime=(ctime_s, ctime_ns),
                                     mtime=(mtime_s,  mtime_ns),
                                     dev=dev,
                                     ino=ino,
                                     mode_type=mode_type,
                                     mode_perms=mode_perms,
                                     uid=uid,
                                     gid=gid,
                                     fsize=fsize,
                                     sha=sha,
                                     flag_assume_valid=flag_assume_valid,
                                     flag_stage=flag_stage,
                                     name=name))

    return GitIndex(version=version, entries=entries)

# Handling the ls-files command
# We will have a --verbose flag instead of all the options provided by Git
# that will show everything

argsp = argsubparsers.add_parser("ls-files", help = "List all the stage files")
argsp.add_argument("--verbose", action="store_true", help="Show everything.")

def cmd_ls_files(args):
    repo = repo_find()
    index = index_parser(repo)
    if args.verbose:
        print(f"Index file format v{index.version}, containing {len(index.entries)} entries.")

    for e in index.entries:
        print(e.name)
        if args.verbose:
            entry_type = { 0b1000: "regular file",
                           0b1010: "symlink",
                           0b1110: "git link" }[e.mode_type]
            print(f"  {entry_type} with perms: {e.mode_perms:o}")
            print(f"  on blob: {e.sha}")
            print(f"  created: {datetime.fromtimestamp(e.ctime[0])}.{e.ctime[1]}, modified: {datetime.fromtimestamp(e.mtime[0])}.{e.mtime[1]}")
            print(f"  device: {e.dev}, inode: {e.ino}")
            print(f"  user: {pwd.getpwuid(e.uid).pw_name} ({e.uid})  group: {grp.getgrgid(e.gid).gr_name} ({e.gid})")
            print(f"  flags: stage={e.flag_stage} assume_valid={e.flag_assume_valid}")

# Handling .gitignore

class GitIgnore(object):
    absolute = None # Global ignore file (~/.config/git/ignore) and repository-specific ignore file (.git/info/exclude)
    scoped = None # Ignore files that only apply to the paths within the directories these reside in

    def __init__(self, absolute, scoped):
        self.absolute = absolute
        self.scoped = scoped


argsp = argsubparsers.add_parser("check-ignore", help = "Check path(s) against ignore rules.")
argsp.add_argument("path", nargs="+", help="Paths to check")

def cmd_check_ignore(args):
    repo = repo_find()
    rules = gitignore_read(repo)
    for path in args.path:
        if check_ignore(rules, path):
            print(path)

# Lines that begin with an exclamation mark ! negate the pattern (files that match this pattern are included, even they were ignored by an earlier pattern)
# Lines that begin with a dash (#) are comments, and are skipped.
# A backslash \ at the beginning treats ! and # as literal characters.

def gitignore_parser(ignore_lines):
    rules_list = list()

    for line in ignore_lines:
        line = line.strip()
        init_char = line[0]
        if init_char and init_char != '#':
            match init_char:
                case '\\': rules_list.append(line[1:], True)
                case '!': rules_list(line[1:], False)
                case _: rules_list(line, True)
    return rules_list
            

def gitignore_read(repo):
    obj = GitIgnore(absolute = list(), scoped = dict())
    # Read local configuration in .git/info/exclude
    repo_ignore_file = repo_file(repo, "info", "exclude")
    if os.path.exists(repo_ignore_file):
        with open(repo_ignore_file, 'r') as file:
            obj.absolute.append(gitignore_parser(file.readlines()))

    # Global configuration ignore file
    config_home = os.environ.get("XDG_CONFIG_HOME", os.path.expanduser("~/.config"))
    global_file = os.path.join(config_home, "git/ignore")
    if os.path.exists(global_file):
        with open(global_file, 'r') as file:
            obj.absolute.append(gitignore_parser(file.readlines()))

    # .gitignore files in the index
    index = index_parser(repo)
    for entry in index.entries:
        if entry.name == ".gitignore" or entry.name.endswith("/.gitignore"):
            dir_name = os.path.dirname(entry.name)
            lines = object_read(repo, entry.sha).blobdata.decode("utf8").splitlines()
            obj.scoped[dir_name] = gitignore_parser(lines)

    return obj

# Priority order: A specific rule has more weight over a general rule.
# A rule that is in an ignore file within a deeper directory is more specific
# A scoped file rule is more specific than absolute file rule
# Within a file, in the order of rules, the last one that is valid for the given path is considered 

def check_ignore_within_file(rules, path):
    result = None
    # rules are processed in order
    for (pattern, value) in rules:
        if fnmatch(path, pattern):
            result = value
    return result

def check_ignore_scoped(rules, path):
    parent = os.path.dirname(path)
    while True:
        if parent in rules:
            result = check_ignore_within_file(rules[parent], path)
            if result != None:
                return result # Deeper the ignore file, the higher its priority over the ignore files in the upper directories
        if parent == "":
            break
        parent = os.path.dirname(parent)
    return None

def check_ignore_absolute(rules, path):
    parent = os.path.dirname(path)
    for ruleset in rules:
        result = check_ignore_within_file(ruleset, path)
        if result != None:
            return result
    return False

def check_ignore(rules, path):
    if os.path.isabs(path):
        raise Exception("This function requires path to be relative to the repository's root")

    result = check_ignore_scoped(rules.scoped, path)
    if result: return result

    return check_ignore_absolute(rules.absolute, path)

# Git Status implementation

argsp = argsubparsers.add_parser("status", help = "Show the working tree status.")

def cmd_status(_):
    repo = repo_find()
    index = index_read(repo)

    status_branch(repo)
    status_head_index(repo, index)
    print()
    status_index_worktree(repo, index)

def status_branch(repo):
    branch = branch_get_active(repo)
    if branch:
        print(f"On branch {branch}.")
    else:
        print(f"HEAD detached at {object_find(repo, 'HEAD')}")

def branch_get_active(repo):
    with open(repo_file(repo, "HEAD"), "r") as f:
        head = f.read()

    head_ref_prefix = "ref: refs/heads/"
    if head.startswith(head_ref_prefix):
        return(head[len(head_ref_prefix):-1])
    else:
        return False

def tree_to_dict(repo, ref, prefix=""):
    ret = dict()
    tree_sha = object_find(repo, ref, fmt=b"tree")
    tree = object_read(repo, tree_sha)

    for leaf in tree.items:
        full_path = os.path.join(prefix, leaf.path)

        is_subtree = leaf.mode.startswith(b'04')

        # Depending on the type, we either store the path (if it's a
        # blob, so a regular file), or recurse (if it's another tree,
        # so a subdir)
        if is_subtree:
            ret.update(tree_to_dict(repo, leaf.sha, full_path))
        else:
            ret[full_path] = leaf.sha
    return ret

def status_head_index(repo, index):
    print("Changes to be committed:")

    head = tree_to_dict(repo, "HEAD")
    for entry in index.entries:
        if entry.name in head:
            if head[entry.name] != entry.sha:
                print("  modified:", entry.name)
            del head[entry.name] # Delete the key
        else:
            print("  added:   ", entry.name)

    # Keys still in HEAD are files that we haven't met in the index,
    # and thus have been deleted.
    for entry in head.keys():
        print("  deleted: ", entry)

def tatus_index_worktree(repo, index):
    print("Changes not staged for commit:")

    ignore = gitignore_read(repo)

    gitdir_prefix = repo.gitdir + os.path.sep

    all_files = list()

    # We begin by walking the filesystem
    for (root, _, files) in os.walk(repo.worktree, True):
        if root==repo.gitdir or root.startswith(gitdir_prefix):
            continue
        for f in files:
            full_path = os.path.join(root, f)
            rel_path = os.path.relpath(full_path, repo.worktree)
            all_files.append(rel_path)

    # We now traverse the index, and compare real files with the cached
    # versions.

    for entry in index.entries:
        full_path = os.path.join(repo.worktree, entry.name)

        # That file *name* is in the index

        if not os.path.exists(full_path):
            print("  deleted: ", entry.name)
        else:
            stat = os.stat(full_path)

            # Compare metadata
            ctime_ns = entry.ctime[0] * 10**9 + entry.ctime[1]
            mtime_ns = entry.mtime[0] * 10**9 + entry.mtime[1]
            if (stat.st_ctime_ns != ctime_ns) or (stat.st_mtime_ns != mtime_ns):
                # If different, deep compare.
                # @FIXME This *will* crash on symlinks to dir.
                with open(full_path, "rb") as path:
                    new_sha = hash_object(path, b"blob", None)
                    # If the hashes are the same, the files are actually the same.
                    same = entry.sha == new_sha

                    if not same:
                        print("  modified:", entry.name)

        if entry.name in all_files:
            all_files.remove(entry.name)

    print()
    print("Untracked files:")

    for f in all_files:
        # @TODO If a full directory is untracked, we should display
        # its name without its contents.
        if not check_ignore(ignore, f):
            print(" ", f)

