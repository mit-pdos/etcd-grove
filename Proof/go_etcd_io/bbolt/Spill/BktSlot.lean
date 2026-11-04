/-
`Bucket.spill` (U9p, `notes/bbolt-proof-plan.md`): **the slots owned at the start of the root
spill**. Before its loop over the cached child buckets, the root spill owns (`slotInv`, at the
spill's mark) the slots of the cached children's unspilled trees (`Dc`, each child's `uTree` slots
`D`, `bk_init`) and the root's own (`rootOwn X Dc`): every other base slot the logical trees cover
(`lCovers`: the root's positions, the uncached nested buckets' trees, the cached children without
a root node). Distinct: within a child's tree its pages are distinct (its nodes' pages by the page
cache, its page positions' subtrees by `posDisjoint`/`posNodeFree`), across the buckets by
`covU` (a child's slots are covered by its positions, `uTree_start_cov`), and `rootOwn` excludes
`Dc`. Owned: a covered base slot is below the committed mark, not free (`mvccView`) and not pending
(`flView`).
-/
module

public import Proof.go_etcd_io.bbolt.Spill.UTree

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

namespace Spill

section slot
variable [GooseExts]

open Classical in
/-- **The root's owned slots at the start of the spill**: the base slots covered by the logical
trees (`lCovers`) but not in the children's trees' slots `Dc`. -/
def rootOwn (X : WX) (Dc : List Nat) : List Nat :=
  (pagesSlots X.v.pages).filter fun s => decide (lCovers X s ∧ s ∉ Dc)

theorem mem_rootOwn {X : WX} {Dc : List Nat} {s : Nat} :
    s ∈ rootOwn X Dc ↔ coversSlot X.v.pages s ∧ lCovers X s ∧ s ∉ Dc := by
  sorry

/-- **A cached child's unspilled tree at the start is covered by its positions** (`c` not the
root: its leaves plain). -/
theorem uTree_start_cov {X : WX} {fl : FLPg} (hpre : spillPre X fl) (hreach : liveReach X)
    {c : Loc} {Cc : BRec} (hc : X.t.bs !! c = some Cc) (hne : c ≠ X.rl)
    {h : Nat} {F D : List Nat} {N : List Loc} {E : List El}
    (hu : uTree X c (spP X) X.t.mv.pgid'.toNat Cc.bv.rootNode' none none h F D N E) :
    D.Nodup ∧ ∀ s ∈ D, coversSlot X.v.pages s ∧ ∃ pid, coverW X s (.pos c pid) := by
  sorry

/-- **A base slot covered other than by a child's position is the root's.** -/
theorem mem_rootOwn_of {X : WX} {fl : FLPg} (hpre : spillPre X fl) (hreach : liveReach X)
    (hv : flViewU X fl) (cs : List (Loc × List Nat))
    (hcs : ∀ c D, (c, D) ∈ cs → c ≠ X.rl ∧ ∃ Cc h F N E, X.t.bs !! c = some Cc ∧
      uTree X c (spP X) X.t.mv.pgid'.toNat Cc.bv.rootNode' none none h F D N E)
    {s : Nat} (hs : coversSlot X.v.pages s) {cw : CovW} (hcw : coverW X s cw)
    (hno : ∀ c D, (c, D) ∈ cs → ∀ pid, cw ≠ .pos c pid) :
    s ∈ rootOwn X (cs.flatMap Prod.snd) := by
  sorry

/-- **The starting slot invariant of the root spill** (see the module doc): the children `cs`
(distinct, none the root), each with its unspilled tree's slots `D` (`bk_init`), and the root's
own slots. -/
theorem slotInv_start {X : WX} {fl : FLPg} {C : CommitSt} (hpre : spillPre X fl)
    (hreach : liveReach X) (hv : flViewU X fl) (hcok : treeOK C) (hcp : X.v.pages = C.pages)
    (hch : C.hwm ≤ X.t.mv.pgid'.toNat)
    (hids : ∀ id ∈ fl.allIds, id.toNat < X.t.mv.pgid'.toNat)
    (cs : List (Loc × List Nat)) (hnd : (cs.map Prod.fst).Nodup)
    (hcs : ∀ c D, (c, D) ∈ cs → c ≠ X.rl ∧ ∃ Cc h F N E, X.t.bs !! c = some Cc ∧
      uTree X c (spP X) X.t.mv.pgid'.toNat Cc.bv.rootNode' none none h F D N E) :
    slotInv fl X.t.mv.pgid'.toNat (rootOwn X (cs.flatMap Prod.snd) ++ cs.flatMap Prod.snd) := by
  sorry

end slot

end Spill

end bbolt
end EtcdGrove
end Perennial
