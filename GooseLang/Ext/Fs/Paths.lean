/-
Paths of the Linux file extension [Trusted definitions!]: names, canonical paths below a root,
textual nesting, a path's last component and directory, used by the extension's directory tree
(`Tree.lean`).

A *name* is a byte string. A *canonical* path below a root `r` is `r` followed by components, each
preceded by `/`, each a valid name (`NameOk`: not empty, not `.` or `..`, no `/`, no NUL): Linux
resolves it component by component, given the environment assumptions (`Impl.lean`). A path that
is not canonical (`r//a`, `r/./a`, `r/a/`) is given no meaning: the steps are stuck on it.
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

end Perennial

end
