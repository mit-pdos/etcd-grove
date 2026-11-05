/-
The namespace of the Linux file extension [Trusted definitions!]: paths, the nodes names map to,
the metadata operations and their replay. The state and the steps that use them are in
`Impl.lean`; the design is `notes/walfs-ext-plan.md`.

**Paths.** A name is a byte string. A *managed* path lies in the tree of a *root* (a directory
fixed at boot), and is the root followed by components, each preceded by `/`, each a valid name
(`NameOk`: not empty, not `.` or `..`, no `/`, no NUL). That is a canonical path: Linux resolves
it component by component to the entry the namespace names, given the environment assumptions
(`Impl.lean`): the roots name distinct directories, no root lies in another's tree, nothing in
their trees is a symlink or a mount point, and no other process changes them. A path that is not
canonical (`r//a`, `r/./a`, `r/a/`) is not given a meaning: the operations are stuck on it.

**Keys.** A file of the namespace is a file of `OsState.files` under a *key* containing a NUL
byte (`IsInoKey`): no path is such a string (Go refuses one, `EINVAL`, before the system call),
so a key is never confused with a name. The key is the inode's identity: an fd names it, so it
follows the file across renames and unlinks, as an fd does on Linux.

**Operations.** Each metadata operation is atomic and is recorded, in order, in the log of
operations not yet known durable (`OsState.nsLog`); `NsOp.apply` is its effect on a namespace,
and `nsReplay` replays a list of them. A crash keeps a prefix of the log (`Impl.lean`, `NsCrash`).
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

noncomputable section

namespace Perennial

/-- `/`. -/
def slashB : w8 := 47

/-- `.`. -/
def dotB : w8 := 46

/-- The NUL byte. -/
def nulB : w8 := 0

/-- A valid name of a directory entry: not empty, not `.` or `..`, no `/`, no NUL. -/
def NameOk (b : GoString) : Prop :=
  b ≠ [] ∧ b ≠ [dotB] ∧ b ≠ [dotB, dotB] ∧ slashB ∉ b ∧ nulB ∉ b

instance (b : GoString) : Decidable (NameOk b) := by unfold NameOk; infer_instance

/-- The path of the components `cs` below `r`: `r/c₁/…/cₙ`. -/
def joinPath (r : GoString) (cs : List GoString) : GoString :=
  r ++ cs.flatMap (fun c => slashB :: c)

/-- `p` is a canonical path strictly below the directory `r`. -/
def CanonBelow (r p : GoString) : Prop :=
  ∃ cs, cs ≠ [] ∧ (∀ c ∈ cs, NameOk c) ∧ p = joinPath r cs

/-- `x` is `d` or lies in `d`'s tree, textually. -/
def IsUnder (d x : GoString) : Prop := x = d ∨ (d ++ [slashB]).IsPrefix x

instance (d x : GoString) : Decidable (IsUnder d x) := by unfold IsUnder; infer_instance

/-- The last component of `p` (all of `p` if it has no `/`). -/
def baseOf (p : GoString) : GoString := (p.reverse.takeWhile (· ≠ slashB)).reverse

/-- The directory `p` is in: `p` up to its last `/`, or nothing if it has none. -/
def parentOf (p : GoString) : Option GoString :=
  let b := baseOf p
  if b.length < p.length then some (p.take (p.length - b.length - 1)) else none

/-- A key of a file of the namespace: it contains a NUL byte, so it is no path. -/
def IsInoKey (k : GoString) : Prop := nulB ∈ k

instance (k : GoString) : Decidable (IsInoKey k) := by unfold IsInoKey; infer_instance

/-- What a name of the namespace is: a file (its key in `OsState.files`), or a directory. -/
inductive OsNode where
  | file (key : GoString)
  | dir
  deriving DecidableEq

/-- A namespace: every managed path that exists, and what it is. -/
abbrev NsMap := GMap GoString OsNode

/-- `x` renamed by the move of `s` to `t`: in `s`'s tree, the same place in `t`'s. -/
def rekey (s t x : GoString) : GoString :=
  if IsUnder s x then t ++ x.drop s.length else x

/-- The namespace `m` with the entry `s`, and its tree if it is a directory, moved to `t`
(nothing at `t` or in its tree). -/
def nsMove (m : NsMap) (s t : GoString) : NsMap :=
  GMap.ofList (m.toList.map (fun kv => (rekey s t kv.1, kv.2)))

/-- A metadata operation, with the paths as they were when it was made. -/
inductive NsOp where
  /-- A new file at `p`, the file of key `key`. -/
  | create (p key : GoString)
  /-- A new directory at `p`. -/
  | mkdir (p : GoString)
  /-- `p` (a file, or an empty directory) removed. -/
  | remove (p : GoString)
  /-- `s` (and its tree) moved to `t`, replacing a file at `t`. -/
  | rename (s t : GoString)

/-- The effect of an operation on a namespace. -/
def NsOp.apply : NsOp → NsMap → NsMap
  | .create p key, m => <[p := .file key]> m
  | .mkdir p, m => <[p := .dir]> m
  | .remove p, m => GMap.delete p m
  | .rename s t, m => nsMove (GMap.delete t m) s t

/-- The operations `ops`, in order, replayed on `m`. -/
def nsReplay (ops : List NsOp) (m : NsMap) : NsMap := ops.foldl (fun m o => o.apply m) m

/-- The directories whose entries the operation changes: the parent of each path it adds or
removes. -/
def NsOp.dirs : NsOp → List GoString
  | .create p _ => (parentOf p).toList
  | .mkdir p => (parentOf p).toList
  | .remove p => (parentOf p).toList
  | .rename s t => (parentOf s).toList ++ (parentOf t).toList

/-- How much of the log `ops` an fsync of the directory `d` commits: up to and including the last
operation that changed `d`'s entries (nothing if none did). The journal commits in order, so
everything before it is committed too. -/
def commitLen (d : GoString) : List NsOp → Nat
  | [] => 0
  | o :: os =>
    let n := commitLen d os
    if 0 < n then n + 1 else if d ∈ o.dirs then 1 else 0

/-- The operation made, removed or moved the path `d` or one above it: before it, `d` may have
named another directory, or none. -/
def NsOp.rebinds (d : GoString) : NsOp → Bool
  | .create p _ => decide (IsUnder p d)
  | .mkdir p => decide (IsUnder p d)
  | .remove p => decide (IsUnder p d)
  | .rename s t => decide (IsUnder s d) || decide (IsUnder t d)

/-- How much of the log an fsync of the directory at `d` is known to commit: `commitLen`, unless
an operation of the log rebinds `d` (then the operations recorded with the path `d` may be of
another directory, and nothing is known to be committed: the journal commits up to the last
change of the directory the fd is on, which the path does not identify). -/
def dirCommitLen (d : GoString) (ops : List NsOp) : Nat :=
  if ops.any (·.rebinds d) then 0 else commitLen d ops

/-- The names (last components) an operation adds to the directory `d`, and those it removes or
changes there. -/
def NsOp.adds (d : GoString) : NsOp → List GoString
  | .create p _ => if parentOf p = some d then [baseOf p] else []
  | .mkdir p => if parentOf p = some d then [baseOf p] else []
  | .remove _ => []
  | .rename _ t => if parentOf t = some d then [baseOf t] else []

def NsOp.touched (d : GoString) : NsOp → List GoString
  | .create p _ => if parentOf p = some d then [baseOf p] else []
  | .mkdir p => if parentOf p = some d then [baseOf p] else []
  | .remove p => if parentOf p = some d then [baseOf p] else []
  | .rename s t => (if parentOf s = some d then [baseOf s] else []) ++
      (if parentOf t = some d then [baseOf t] else [])

/-- The names in the directory `d` of the namespace `m`. -/
def entryIn (m : NsMap) (d b : GoString) : Prop := (m !! (d ++ slashB :: b)).isSome

end Perennial

end
