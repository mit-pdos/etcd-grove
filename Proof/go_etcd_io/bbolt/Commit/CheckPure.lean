/-
The pure facts `freepages`' check needs of a `treeOK` view (U10e of
`notes/bbolt-proof-plan.md`): a root's walk (`pageWalk`) visits each of its own pages
(`ownHas`) once, each a well-formed branch or leaf; the slots of a root's own pages
(`ownSlot`).
-/
module

public import Proof.go_etcd_io.bbolt.Model.WOps
public import Proof.go_etcd_io.bbolt.Model.Mvcc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- Slot `s` is covered by one of the own pages of the tree from `r`. -/
def ownSlot (P : Pages) (r s : Nat) : Prop :=
  ∃ id pg, ownHas P r id ∧ P !! id = some pg ∧ id ≤ s ∧ s ≤ id + pageOverflow pg

/-- `r` is a root of a tree of the `treeOK` pages `P` (the root bucket's, or a nested bucket's
stored in pages): well-formed, its keys a B+tree's. -/
def ownRootOK (P : Pages) (r : Nat) : Prop :=
  ∃ C : CommitSt, treeOK C ∧ C.pages = P ∧ C.hwm ≤ 2 ^ 62 ∧ treeWF P C.hwm r ∧
    treeKeys P r none none

/-- **A page of a root's walk** is one of its own pages, a well-formed branch or leaf, its
header's id its own, inside the high-water mark. -/
theorem walk_entry (P : Pages) (r : Nat) (h : ownRootOK P r) (k id : Nat) (ids : List Nat)
    (hk : (pageWalk P r)[k]? = some (id, ids)) :
    ∃ pg, P !! id = some pg ∧ ownHas P r id ∧ pageId pg = id ∧ 16 ≤ pg.length ∧
      (pageFlags pg = branchPageFlag ∨ pageFlags pg = leafPageFlag) ∧
      id + (1 + pageOverflow pg) ≤ 2 ^ 62 := by
  sorry

/-- **A root's walk visits each page once.** -/
theorem walk_nodup (P : Pages) (r : Nat) (h : ownRootOK P r) :
    ((pageWalk P r).map Prod.fst).Nodup := by
  sorry

/-- **A root's walk visits all its own pages.** -/
theorem walk_cover (P : Pages) (r : Nat) (h : ownRootOK P r) (id : Nat) (ho : ownHas P r id) :
    ∃ (k : Nat) (ids : List Nat), (pageWalk P r)[k]? = some (id, ids) := by
  sorry

/-- Slot `x` is covered by one of the first `i` pages of the walk of `r`. -/
def walkSlot (P : Pages) (r i x : Nat) : Prop :=
  ∃ j < i, ∃ id ids pg, (pageWalk P r)[j]? = some (id, ids) ∧ P !! id = some pg ∧ id ≤ x ∧
    x ≤ id + pageOverflow pg

/-- **The `i`-th page of the walk shares no slot with the earlier ones.** -/
theorem walkSlot_disj (P : Pages) (r : Nat) (h : ownRootOK P r) (i id : Nat) (ids : List Nat)
    (pg : List w8) (hi : (pageWalk P r)[i]? = some (id, ids)) (hpg : P !! id = some pg) (x : Nat)
    (hx : walkSlot P r i x) : ¬ (id ≤ x ∧ x ≤ id + pageOverflow pg) := by
  sorry

/-- **The walk's pages' slots are the own pages' slots.** -/
theorem walkSlot_all (P : Pages) (r : Nat) (h : ownRootOK P r) (x : Nat) :
    walkSlot P r (pageWalk P r).length x ↔ ownSlot P r x := by
  sorry

end pure

end bbolt
end EtcdGrove
end Perennial
