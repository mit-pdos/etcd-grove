/-
**The shared `wOK_nodeAdded` and `wtxData_matGrow`** (batch 22's move, `notes/bbolt-proof-plan.md`):
U7b's `wOK_nodeAdded'` (`Write/MatOK`) with its three premises discharged, from `nodeAdded`'s
clauses (batch 20: the new node's nested buckets' value sources, the parent's `capOwn`) and
`bktClean`'s inline clause (batch 22: `inlineBnd`); `wtxData_matGrow` (moved from `Write/Mat`) by
induction over it.
-/
module

public import Proof.go_etcd_io.bbolt.Write.MatOK

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section grow
variable [GooseExts]

/-- **Materializing a page position keeps `wOK`** (the shared statement, formerly a `sorry` in
`Model/WOps`): the root page of a bucket with no root node, or a child its branch node has not
materialized. -/
theorem wOK_nodeAdded (X X' : WX) (bl l : Loc) (pgid : w64) (parent : Loc)
    (hok : wOK X) (h : nodeAdded X X' bl l pgid parent) (hpos : matPos X bl pgid parent) :
    wOK X' := by
  have h' := h
  obtain ⟨B, pa, pg, r, ns', bv', hB, -, -, hl0, hlo, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hrvs, hcase, hX'⟩ := h'
  have hlo' : X.t.objs !! l = none := by simpa using hlo
  have hfresh : B.ns !! l = none := objs_none X.t l hlo' bl B hB
  have hB' : X'.t.bs !! bl = some { B with nm := B.nm.insert pgid l, ns := ns', bv := bv' } := by
    rw [hX']; exact GMap.lookup_insert _ _ _
  refine wOK_nodeAdded' X X' bl l pgid parent hok h hpos ?_ ?_ ?_
  · intro B' r' hb' hr'
    rw [hB'] at hb'; cases hb'
    have hns'l : ns' !! l = some r := by
      rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, rp, rp', -, -, -, -, -, -, -, -, -, rfl⟩ <;>
        exact GMap.lookup_insert _ _ _
    have : r' = r := by
      have e : ns' !! l = some r' := hr'
      rw [hns'l] at e; cases e; rfl
    subst this
    exact hrvs
  · intro B0 B1 rp0 rp1 hb0 hb1 hrp0 hrp1
    rw [hB] at hb0; cases hb0
    rw [hB'] at hb1; cases hb1
    have hpl : parent ≠ l := by intro e; rw [e, hfresh] at hrp0; cases hrp0
    rcases hcase with ⟨-, -, rfl⟩ | ⟨-, -, rp, rp', hrp, -, -, -, -, -, -, hco, -, rfl⟩
    · have e : (B.ns.insert l r) !! parent = some rp1 := hrp1
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hpl), hrp0] at e
      cases e; rfl
    · have e : ((B.ns.insert parent rp').insert l r) !! parent = some rp1 := hrp1
      rw [GMap.lookup_insert_ne _ _ (Ne.symm hpl), GMap.lookup_insert] at e
      cases e
      rw [hrp0] at hrp; cases hrp
      exact hco
  · intro B0 hb0 h0 hrn j hj
    have hc := wOK_bktClean X hok bl B0 hb0
    exact (hc.1 h0 hrn).2.2.2 j hj

/-- **Materializations keep the writer's data** (`Model/WOps`' former `wtxData_matGrow`, with
`wOK` at the start: each step keeps it, `wOK_nodeAdded`, and gives the step's freshness). -/
theorem wtxData_matGrow (X X' : WX) (bl : Loc) (hok : wOK X) (h : matGrow X X' bl) :
    wtxData X' = wtxData X := by
  revert hok
  induction h with
  | refl => intro _; rfl
  | step X Y Z bl l pgid parent hadd hpos _ ih =>
    intro hok
    rw [ih (wOK_nodeAdded X Y bl l pgid parent hok hadd hpos)]
    exact wtxData_nodeAdded' X Y bl l pgid parent hadd
      (wOK_matFresh X Y bl l pgid parent hok hadd hpos) (wOK_inlineLeaf X bl pgid hok)

end grow

end Write

end bbolt
end EtcdGrove
end Perennial
