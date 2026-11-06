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
order: an operation that took effect before another's call began is journaled before it; two that
change a common directory are serialized by that directory's lock, so the journal has them in the
log's order; two renames across directories are serialized by the filesystem's rename lock. Two
operations related by none of these change disjoint directories, so they commute.
-/
module

public import GooseLang.Ext.Fs.Paths

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

/-- The directory inode a node is, if it is one. -/
def Node.dirIno : Node → List Ino
  | .file _ => []
  | .dir j => [j]

/-- What the entry `b` of the directory `j` names. -/
def Tree.entry (m : Tree) (j : Ino) (b : GoString) : Option Node := (m !! j).bind (· !! b)

/-- `m` with the entries of the directory `j` changed by `f`. -/
def Tree.upd (m : Tree) (j : Ino) (f : Dir → Dir) : Tree := <[j := f ((m !! j).getD ∅)]> m

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

/-- The effect of an operation on a tree. A directory's subtree moves with its entry. A removed
directory's inode keeps its (empty) entries. -/
def MetaOp.apply : MetaOp → Tree → Tree
  | .create j b i, m => m.upd j (fun d => <[b := .file i]> d)
  | .mkdir j b j', m => <[j' := ∅]> (m.upd j (fun d => <[b := .dir j']> d))
  | .remove j b _, m => m.upd j (fun d => GMap.delete b d)
  | .rename j b j' b' _ _, m => match m.entry j b with
    | some n => (m.upd j (fun d => GMap.delete b d)).upd j' (fun d => <[b' := n]> d)
    | none => m

/-- The operations `ops`, in order, replayed on `m`. -/
def replay (ops : List MetaOp) (m : Tree) : Tree := ops.foldl (fun m o => o.apply m) m

/-- The directories an operation changes or locks: the directories whose entries it changes, the
directory it creates, and a directory it removes, moves or replaces. -/
def MetaOp.dirs : MetaOp → List Ino
  | .create j _ _ => [j]
  | .mkdir j _ j' => [j, j']
  | .remove j _ n => j :: n.dirIno
  | .rename j _ j' _ n old => [j, j'] ++ n.dirIno ++ (old.map Node.dirIno).getD []

/-- A rename from one directory to another (Linux serializes them per filesystem). -/
def MetaOp.crossRename : MetaOp → Bool
  | .rename j _ j' _ _ _ => decide (j ≠ j')
  | _ => false

/-- The names an operation adds to the directory `j`. -/
def MetaOp.adds (j : Ino) : MetaOp → List GoString
  | .create j0 b _ => if j0 = j then [b] else []
  | .mkdir j0 b _ => if j0 = j then [b] else []
  | .remove _ _ _ => []
  | .rename _ _ j1 b' _ _ => if j1 = j then [b'] else []

/-- The names an operation adds to, removes from or changes in the directory `j`. -/
def MetaOp.touched (j : Ino) : MetaOp → List GoString
  | .create j0 b _ => if j0 = j then [b] else []
  | .mkdir j0 b _ => if j0 = j then [b] else []
  | .remove j0 b _ => if j0 = j then [b] else []
  | .rename j0 b j1 b' _ _ => (if j0 = j then [b] else []) ++ (if j1 = j then [b'] else [])

/-- A logged operation and the length of the log when its call began: the operations before that
had taken effect (and returned) before it began. -/
structure LogEntry where
  op : MetaOp
  start : Nat

/-- The entry `y` of the log must survive a crash that keeps the entry `x`: `y` took effect before
`x`'s call began, or `y` is earlier and they change or lock a common directory, or both are renames
across directories. -/
def Follows (log : List LogEntry) (x y : Nat) : Prop :=
  y < x ∧ ∃ ex ey, log[x]? = some ex ∧ log[y]? = some ey ∧
    (y < ex.start ∨ (∃ j, j ∈ ex.op.dirs ∧ j ∈ ey.op.dirs) ∨
      (ex.op.crossRename = true ∧ ey.op.crossRename = true))

/-- A set of entries closed under `Follows`: what a crash may keep. -/
def Closed (log : List LogEntry) (S : Nat → Prop) : Prop :=
  ∀ x y, S x → Follows log x y → S y

/-- The entries that must be on disk once `x` is: `x`, and what it follows, transitively. -/
inductive Needed (log : List LogEntry) (x : Nat) : Nat → Prop where
  | self : Needed log x x
  | step (y z : Nat) : Needed log x y → Follows log y z → Needed log x z

open Classical in
/-- The operations of the entries of `log` in `S`, in log order. -/
def keptOps (log : List LogEntry) (S : Nat → Prop) : List MetaOp :=
  (List.range log.length).filterMap (fun k => if S k then (log[k]?).map (·.op) else none)

/-- The last entry of the log that changes or locks the directory `j`. -/
def lastTouch (log : List LogEntry) (j : Ino) : Option Nat :=
  ((List.range log.length).filter (fun k => decide (∃ e, log[k]? = some e ∧ j ∈ e.op.dirs))).getLast?

/-- The roots: distinct paths, canonical and absolute (`RootForm`), none in another's tree. -/
def RootForm (r : GoString) : Prop :=
  ∃ cs, cs ≠ [] ∧ (∀ c ∈ cs, NameOk c) ∧ r = joinPath [] cs

def RootsOk (roots : List (GoString × Ino)) : Prop :=
  (roots.map (·.1)).Nodup ∧ (roots.map (·.2)).Nodup ∧
  ∀ r ∈ roots, RootForm r.1 ∧ ∀ r' ∈ roots, r.1 ≠ r'.1 → ¬ IsUnder r.1 r'.1

/-- The directory `j` is reachable from a root of `roots` in `m`. -/
inductive Reach (roots : List (GoString × Ino)) (m : Tree) : Ino → Prop where
  | root (r : GoString) (j : Ino) : (r, j) ∈ roots → Reach roots m j
  | child (j : Ino) (b : GoString) (j' : Ino) :
      Reach roots m j → m.entry j b = some (.dir j') → Reach roots m j'

/-- `m` is a tree over `roots`: every directory reachable from a root; each directory named once
(by a root or by one entry, so no cycle) and each file named once (no hard links); every entry's
name valid and every directory it names one of `m`'s. -/
def TreeWf (roots : List (GoString × Ino)) (m : Tree) : Prop :=
  (∀ j, j ∈ m ↔ Reach roots m j) ∧
  (∀ j b n, m.entry j b = some n → NameOk b ∧ ∀ j' ∈ n.dirIno, j' ∈ m) ∧
  (∀ j b j', m.entry j b = some (.dir j') → ∀ r, (r, j') ∉ roots) ∧
  (∀ j1 b1 j2 b2 n, m.entry j1 b1 = some n → m.entry j2 b2 = some n → j1 = j2 ∧ b1 = b2)

end Fs
end Perennial

end
