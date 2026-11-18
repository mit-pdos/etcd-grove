/-
The pure model of the interval tree's red-black tree (`pkg/v3/adt`): the tree as an inductive
(`RbT`: the sentinel is the leaf), its in-order list, the red-black invariant (`RbOk`), the
subtrees' `max` augmentation (`RbT.maxEnd`, `nodeMax`), the rotations, and the reads' descents
as pure functions mirroring the Go code (`findE`, `intersects`, `visitL`) with their
correctness over the in-order list (`findE_some`/`findE_none`, `intersects_iff`, `visit_stab`). Lean-first; see
`notes/decisions.md`, "The watchable store: the plan, the interval tree's contract".
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.Model

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace adt

/-! ## The tree -/

/-- A node's colour (`rbcolor`: `black` is `0`, `red` is `1`). -/
inductive RbColor where
  | red
  | black
  deriving DecidableEq

/-- The tree: a leaf (the sentinel), or a node with its colour, its children and its entry. -/
inductive RbT (E : Type) where
  | leaf : RbT E
  | node (c : RbColor) (l : RbT E) (e : E) (r : RbT E) : RbT E

namespace RbT
variable {E : Type}

/-- The entries in order (left subtree, the node, right subtree). -/
def inorder : RbT E → List E
  | leaf => []
  | node _ l e r => l.inorder ++ e :: r.inorder

/-- The colour (`color(sentinel)`: the sentinel is black). -/
def color : RbT E → RbColor
  | leaf => .black
  | node c _ _ _ => c

/-- `some h` when every path from the root to a leaf has `h` black nodes. -/
def blackHeight : RbT E → Option Nat
  | leaf => some 0
  | node c l _ r =>
    match l.blackHeight, r.blackHeight with
    | some a, some b => if a = b then some (a + if c = .black then 1 else 0) else none
    | _, _ => none

/-- A red node has black children (the sentinel is black). -/
def redOk : RbT E → Prop
  | leaf => True
  | node c l _ r => (c = .red → l.color = .black ∧ r.color = .black) ∧ l.redOk ∧ r.redOk

end RbT

/-! ## The affine order, more -/

/-! ## Overlap -/

section entries
variable [GooseExts]
set_option linter.unusedSectionVars false

/-! ## Sorted trees -/

/-- Entries sorted by the tree's order, non-strictly: equal intervals are allowed (`Insert`
puts a new one after the equal ones), none is above a later one. -/
def IvSorted (L : List Entry) : Prop := L.Pairwise fun a b => ¬ ivlLt b.1 a.1

/-! ## The `max` augmentation -/

/-- `updateMax`'s step: the larger of `m` and the child's max (if any), under `affCmp`. -/
def affMaxO (m : GoString) : Option GoString → GoString
  | none => m
  | some x => if affCmp x m > 0 then x else m

/-- The largest end of a subtree's entries; `none` for the leaf. -/
def RbT.maxEnd : RbT Entry → Option GoString
  | .leaf => none
  | .node _ l e r => some (affMaxO (affMaxO e.1.2 l.maxEnd) r.maxEnd)

/-- A node's `max` field: its end, then its children's max (as `updateMax` computes it). -/
def nodeMax (l : RbT Entry) (e : Entry) (r : RbT Entry) : GoString :=
  affMaxO (affMaxO e.1.2 l.maxEnd) r.maxEnd

/-! ## `find` -/

/-! ## `Intersects` -/

/-! ## `visit` (`Stab`, `Visit`) -/

end entries

/-! ## The red-black invariant -/

section rb
variable [GooseExts]

/-- The root is black (after `insertFixup`'s and `deleteFixup`'s last line). -/
def rootBlack (t : RbT Entry) : Prop := t.color = .black

/-- The red-black invariant: a red node's children are black, the black height is the same on
every path, the root is black. -/
def RbOk (t : RbT Entry) : Prop := t.redOk ∧ t.blackHeight.isSome ∧ rootBlack t

end rb

end adt
end EtcdGrove
end Perennial
