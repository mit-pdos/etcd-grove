/-
The directory tree of the Linux file extension [Trusted definitions!]: directories and their
entries, the metadata operations and their replay, the order a crash must respect. The state and
the steps that use them are in `Impl.lean`; the design is `notes/fs-semantics-v2.md`.

**The tree.** Every directory, by its inode number, with its entries: a name, and the file or
directory it names (`Node`). Inode numbers (`Ino`) are internal to the model: no step takes or
returns one. Paths are resolved by walking from a root (`Impl.lean`, `OsState.lookup`). POSIX calls
the tree the file hierarchy; Linux implements it as directory entries (dentries), and journals each
change as a change of a directory's entries.

**Metadata operations** (`MetaOp`): `create`, `mkdir`, `remove`, `rename`, by directory inode and
name, as the journal records them (so that replaying some of them gives a tree whatever the others
did to the paths above). Each is atomic and logged in the order the calls took effect
(`FsState.metaLog`), with the length of the log when its call began (`LogEntry.start`). A crash keeps
a set of logged operations closed under `Follows` (`Impl.lean`, `MachineCrash`), replayed in log
order: an operation that took effect before another's call began is journaled before it (one
journal, committing whole transactions in order: a call that began after another returned joins a
transaction no earlier than the other's). Nothing else orders them: two overlapping calls may be
kept in either combination, even when Linux serializes them (a directory's lock, the rename lock),
which only allows more crashes than Linux has.
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

/-- An inode number: a file's or a directory's identity, internal to the model. -/
abbrev Ino := Nat

/-- What a directory entry names: a file or a directory, by inode. -/
inductive Node where
  | file (i : Ino)
  | dir (j : Ino)
  deriving DecidableEq

/-- A directory's entries: each name (a valid one, `NameOk`), and what it names. -/
abbrev Dir := GMap GoString Node

/-- The directories, by inode. -/
abbrev Tree := GMap Ino Dir

/-- A metadata operation, as journaled: by directory inode and name. A removal and a rename also
record what they removed or moved, and what a rename replaced (which they lock, and which a crash's
order must respect). -/
inductive MetaOp where
  /-- A new file of inode `i`, named `b` in the directory `j`. -/
  | create (j : Ino) (b : GoString) (i : Ino)
  /-- A new, empty directory of inode `j'`, named `b` in the directory `j`. -/
  | mkdir (j : Ino) (b : GoString) (j' : Ino)
  /-- The entry `b` of the directory `j` removed: it named `n` (a file, or an empty directory). -/
  | remove (j : Ino) (b : GoString) (n : Node)
  /-- The entry `b` of the directory `j`, naming `n`, moved to the name `b'` of the directory `j'`,
  replacing what that named (`old`: a file, or an empty directory). -/
  | rename (j : Ino) (b : GoString) (j' : Ino) (b' : GoString) (n : Node) (old : Option Node)

/-- A logged operation and the length of the log when its call began: the operations before that
had taken effect (and returned) before it began. -/
structure LogEntry where
  op : MetaOp
  start : Nat

end Fs
end Perennial

end
