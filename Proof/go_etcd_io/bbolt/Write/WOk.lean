/-
U7's (`notes/bbolt-proof-plan.md`) facts `wOK` gives a materialization: the new node is fresh in
its bucket (`wOK_matFresh`), and an inline bucket's page, read while it has no root node, is a
leaf (`wOK_inlineLeaf`; `Model/WOps`' `wOK_inlineLeaf` lacks the `rootNode = nil` premise and is
false without it: `bktClean`'s `inlineGood` is only for a bucket with no root node).
-/
module

public import Proof.go_etcd_io.bbolt.Write.Heap

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section wok
variable [GooseExts]

theorem wOK_bktClean (X : WX) (hok : wOK X) (bl : Loc) (B : BRec) (hb : X.t.bs !! bl = some B) :
    bktClean X.v X.t.mv.pgid'.toNat bl B :=
  (hok.1.2.2.2.2.2 bl B hb).1

/-- `wOK_matFresh` (`Model/WOps`). -/
theorem wOK_matFresh (X X' : WX) (bl l : Loc) (pgid : w64) (parent : Loc) (hok : wOK X)
    (h : nodeAdded X X' bl l pgid parent) (hpos : matPos X bl pgid parent) : matFresh X bl l := by
  obtain ⟨B0, -, -, -, -, -, hB0, -, -, -, hlo, -⟩ := h
  intro B hB
  have hc := wOK_bktClean X hok bl B hB
  refine ⟨fun c hc' => ?_, fun hin => ?_⟩
  · obtain ⟨-, r, hr, -⟩ := hc.2.2.2.2.1 c l hc'
    have := objs_isSome_node X.t bl B l hB (by simp [hr])
    simp_all
  · obtain ⟨B1, hB1, hp⟩ := hpos
    rw [hB] at hB1; cases hB1
    rcases hp with ⟨-, hrn, -⟩ | ⟨i, r, w, hr, hleaf, -⟩
    · exact hrn
    · have := hc.2.2.2.2.2.2.1 hin parent r hr
      rw [hleaf] at this; cases this

/-- `wOK_inlineLeaf` with the inline bucket's root node nil (what a materialization of it
reads: `matFresh`). -/
theorem wOK_inlineLeaf (X : WX) (bl : Loc) (pgid : w64) (hok : wOK X) :
    ∀ B pa pg, X.t.bs !! bl = some B → B.ib.root' = W64 0 → B.bv.rootNode' = null →
      wpageAt X.v B pgid = some (pa, pg) → pageFlags pg = leafPageFlag := by
  intro B pa pg hB hin hrn hpg
  have hc := wOK_bktClean X hok bl B hB
  obtain ⟨-, -, hg, -⟩ := hc.1 hin hrn
  unfold wpageAt at hpg
  rw [if_pos hin] at hpg
  split at hpg
  · simp only [Option.some.injEq, Prod.mk.injEq] at hpg
    obtain ⟨-, rfl⟩ := hpg
    exact hg.2.1
  · cases hpg

end wok

end Write

end bbolt
end EtcdGrove
end Perennial
