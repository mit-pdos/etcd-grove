/-
`tracker.ProgressTracker.IsSingleton`, Lean-first.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__IsSingleton

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The two field reads go through `trk ↦{dq} tv` (the access instances of `Config`'s
`Voters` and `JointConfig`'s halves); each `len` is `wp_idset_len`, whose size bound turns the
`int` comparisons into ones on the sizes. -/
theorem tracker.ProgressTracker.IsSingleton.wp_proof :
    tracker.ProgressTracker.IsSingleton.spec (GF := GF) (hG := hG) := by
  intro trk dq tv v0 v1 dq0 dq1 s0 s1 Harr
  obtain ⟨H0, H1⟩ := (quorum.JointConfig.halves_eq _ _ _).1 Harr
  wp_start as ⟨Htrk, H0', H1'⟩
  wp_auto
  icases (Access.access
      (A := trk.[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Voters"].[quorum.JointConfig, go!"Incoming"] ↦{dq}
        tv.Config'.Voters'.Incoming')
      (A' := trk.[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Voters"].[quorum.JointConfig, go!"Incoming"] ↦{dq}
        tv.Config'.Voters'.Incoming')
      (P := trk ↦{dq} tv)) $$ Htrk with ⟨Hf, Htrkback⟩
  wp_auto
  ihave Htrk := Htrkback $$ Hf
  rw [H0]
  wp_apply wp_idset_len $$ H0' as ⟨H0', %Hlt0⟩
  wp_if_destruct
  · icases (Access.access
        (A := trk.[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Voters"].[quorum.JointConfig, go!"Outgoing"] ↦{dq}
          tv.Config'.Voters'.Outgoing')
        (A' := trk.[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Voters"].[quorum.JointConfig, go!"Outgoing"] ↦{dq}
          tv.Config'.Voters'.Outgoing')
        (P := trk ↦{dq} tv)) $$ Htrk with ⟨Hf, Htrkback⟩
    wp_auto
    ihave Htrk := Htrkback $$ Hf
    rw [H1]
    wp_apply wp_idset_len $$ H1' as ⟨H1', %Hlt1⟩
    rw [show decide (W64 (GMap.size s1 : Int) = W64 0) =
        decide (GMap.size s0 = 1 ∧ GMap.size s1 = 0) from by
      apply decide_eq_decide.2
      constructor
      · intro h; exact ⟨by word, by word⟩
      · intro h; rw [h.2]; rfl]
    iapply HΦ
    iframe
  · rw [show decide (GMap.size s0 = 1 ∧ GMap.size s1 = 0) = false from by
      apply decide_eq_false
      intro h; apply Hif; rw [h.1]; rfl]
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
