/-
The directory tree of the Linux file extension [Trusted definitions!]: what a path names, the
metadata operations and their replay, what a directory `fsync` commits. The state and the steps
that use them are in `Impl.lean`; the design is `notes/fs-semantics-v2.md`.

**The tree.** Every canonical path in a root's tree that exists, and what it is: a directory, or a
file, by its inode number (`Ino`: internal to the model; no step takes or returns one). Directories
have no identity of their own: a directory is its path. POSIX calls the tree the file hierarchy;
Linux implements it as directory entries.

**Metadata operations.** `create`, `mkdir`, `remove`, `rename` (`MetaOp`), each atomic, recorded in
order in the log of operations made since the last journal commit the model knows of
(`FsState.metaLog`); `MetaOp.apply` is the effect of one on a tree, `replay` of a list. A crash
keeps a prefix of the log (`Impl.lean`, `OsCrash`): ext4 and xfs put metadata operations in their
journal in the order they are made and commit the journal in order. A `create` records the inode
the step chose, so that a replay names the file the program has been using.
-/
module

public import GooseLang.Ext.Fs.Paths

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

/-- An inode number: a file's identity, internal to the model. -/
abbrev Ino := Nat

/-- What a path of the tree is: a file (its inode) or a directory. -/
inductive Node where
  | file (i : Ino)
  | dir
  deriving DecidableEq

/-- A directory tree: every canonical path in a root's tree that exists, and what it is. -/
abbrev Tree := GMap GoString Node

/-- `x` renamed by the move of `s` to `t`: in `s`'s tree, the same place in `t`'s. -/
def rekey (s t x : GoString) : GoString :=
  if IsUnder s x then t ++ x.drop s.length else x

/-- The tree `m` with the entry `s`, and its subtree if it is a directory, moved to `t` (nothing
at `t` or in its tree). -/
def moveTree (m : Tree) (s t : GoString) : Tree :=
  GMap.ofList (m.toList.map (fun kv => (rekey s t kv.1, kv.2)))

/-- A metadata operation, with the paths as they were when it was made. -/
inductive MetaOp where
  /-- A new file at `p`, the file of inode `i`. -/
  | create (p : GoString) (i : Ino)
  /-- A new directory at `p`. -/
  | mkdir (p : GoString)
  /-- `p` (a file, or an empty directory) removed. -/
  | remove (p : GoString)
  /-- `s` (and its subtree) moved to `t`, replacing a file or an empty directory at `t`. -/
  | rename (s t : GoString)

/-- The effect of an operation on a tree. A rename of a file moves its entry (replacing one at
`t`); of a directory, its subtree (`moveTree`; an empty directory at `t` is replaced). -/
def MetaOp.apply : MetaOp → Tree → Tree
  | .create p i, m => <[p := .file i]> m
  | .mkdir p, m => <[p := .dir]> m
  | .remove p, m => GMap.delete p m
  | .rename s t, m => match m !! s with
    | some (.file i) => <[t := .file i]> (GMap.delete s m)
    | _ => moveTree (GMap.delete t m) s t

/-- The operations `ops`, in order, replayed on `m`. -/
def replay (ops : List MetaOp) (m : Tree) : Tree := ops.foldl (fun m o => o.apply m) m

/-- The directories whose entries the operation changes: the parent of each path it adds or
removes. -/
def MetaOp.dirs : MetaOp → List GoString
  | .create p _ => (parentOf p).toList
  | .mkdir p => (parentOf p).toList
  | .remove p => (parentOf p).toList
  | .rename s t => (parentOf s).toList ++ (parentOf t).toList

/-- How much of the log `ops` an fsync of the directory `d` commits: up to and including the last
operation that changed `d`'s entries (nothing if none did). The journal commits in order, so
everything before it is committed too. -/
def commitLen (d : GoString) : List MetaOp → Nat
  | [] => 0
  | o :: os =>
    let n := commitLen d os
    if 0 < n then n + 1 else if d ∈ o.dirs then 1 else 0

/-- The operation made, removed or moved the path `d` or one above it: before it, `d` may have
named another directory, or none. -/
def MetaOp.rebinds (d : GoString) : MetaOp → Bool
  | .create p _ => decide (IsUnder p d)
  | .mkdir p => decide (IsUnder p d)
  | .remove p => decide (IsUnder p d)
  | .rename s t => decide (IsUnder s d) || decide (IsUnder t d)

/-- How much of the log an fsync of the directory at `d` is known to commit: `commitLen`, unless
an operation of the log rebinds `d` (then the operations recorded with the path `d` may be of
another directory, and nothing is known to be committed: the journal commits up to the last change
of the directory the fd is on, which the path does not identify). -/
def dirCommitLen (d : GoString) (ops : List MetaOp) : Nat :=
  if ops.any (·.rebinds d) then 0 else commitLen d ops

/-- The names (last components) an operation adds to the directory `d`. -/
def MetaOp.adds (d : GoString) : MetaOp → List GoString
  | .create p _ => if parentOf p = some d then [baseOf p] else []
  | .mkdir p => if parentOf p = some d then [baseOf p] else []
  | .remove _ => []
  | .rename _ t => if parentOf t = some d then [baseOf t] else []

/-- The names an operation adds to, removes from or changes in the directory `d`. -/
def MetaOp.touched (d : GoString) : MetaOp → List GoString
  | .create p _ => if parentOf p = some d then [baseOf p] else []
  | .mkdir p => if parentOf p = some d then [baseOf p] else []
  | .remove p => if parentOf p = some d then [baseOf p] else []
  | .rename s t => (if parentOf s = some d then [baseOf s] else []) ++
      (if parentOf t = some d then [baseOf t] else [])

/-- `b` is a name in the directory `d` of the tree `m`. -/
def entryIn (m : Tree) (d b : GoString) : Prop := NameOk b ∧ (m !! (d ++ slashB :: b)).isSome

/-- A root's form: canonical and absolute (`/c₁/…/cₙ`, `n ≥ 1`), so that textual nesting is
nesting and no root is relative to a working directory. -/
def RootForm (r : GoString) : Prop :=
  ∃ cs, cs ≠ [] ∧ (∀ c ∈ cs, NameOk c) ∧ r = joinPath [] cs

/-- The roots: distinct, canonical, none in another's tree. -/
def RootsOk (roots : List GoString) : Prop :=
  roots.Nodup ∧ ∀ r ∈ roots, RootForm r ∧ ∀ r' ∈ roots, r ≠ r' → ¬ IsUnder r r'

/-- `m` is a tree over `roots`: each root a directory; every other path canonical in a root's
tree, in a directory of `m`; no file named twice (no hard links). -/
def TreeShape (roots : List GoString) (m : Tree) : Prop :=
  (∀ r ∈ roots, m !! r = some .dir) ∧
  (∀ p x, m !! p = some x → p ∈ roots ∨
    ((∃ r ∈ roots, CanonBelow r p) ∧ ∃ d, parentOf p = some d ∧ m !! d = some .dir)) ∧
  (∀ p q i, m !! p = some (.file i) → m !! q = some (.file i) → p = q)

end Fs
end Perennial

end
