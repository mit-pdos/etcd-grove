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

/-- The two element reads go through the `Voters` field of `trk ↦{dq} tv`
(`Access.access`) and `array_acc`, put back unchanged (`Hset0`, `Hset1`); each `len` is
`wp_idset_len`, whose size bound turns the `int` comparisons into ones on the sizes. -/
theorem tracker.ProgressTracker.IsSingleton.wp_proof :
    tracker.ProgressTracker.IsSingleton.spec (GF := GF) (hG := hG) := by
  intro trk dq tv v0 v1 dq0 dq1 s0 s1 Harr
  have Hset0 : array.mk 2 (tv.Config'.Voters'.arr.set (sint.Z (W64 0)).toNat v0) =
      tv.Config'.Voters' := by
    generalize tv.Config'.Voters' = a at Harr ⊢
    cases a
    simp only at Harr
    subst Harr
    rfl
  have Hset1 : array.mk 2 (tv.Config'.Voters'.arr.set (sint.Z (W64 1)).toNat v1) =
      tv.Config'.Voters' := by
    generalize tv.Config'.Voters' = a at Harr ⊢
    cases a
    simp only at Harr
    subst Harr
    rfl
  wp_start as ⟨Htrk, H0, H1⟩
  wp_auto
  icases (Access.access
      (A := trk.[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Voters"] ↦{dq}
        tv.Config'.Voters')
      (A' := trk.[tracker.ProgressTracker, go!"Config"].[tracker.Config, go!"Voters"] ↦{dq}
        tv.Config'.Voters')
      (P := trk ↦{dq} tv)) $$ Htrk with ⟨Hvf, Htrkback⟩
  icases array_acc _ (sint.Z (W64 0)) _ _ _ v0 (by decide) (by rw [Harr]; rfl)
    $$ Hvf with ⟨Hc0, Hcback⟩
  wp_auto
  ihave Hvf := Hcback $$ Hc0
  rw [Hset0]
  wp_apply wp_idset_len $$ H0 as ⟨H0, %Hlt0⟩
  wp_if_destruct
  · icases array_acc _ (sint.Z (W64 1)) _ _ _ v1 (by decide) (by rw [Harr]; rfl)
      $$ Hvf with ⟨Hc1, Hcback⟩
    wp_auto
    ihave Hvf := Hcback $$ Hc1
    rw [Hset1]
    ihave Htrk := Htrkback $$ Hvf
    wp_apply wp_idset_len $$ H1 as ⟨H1, %Hlt1⟩
    rw [show decide (W64 (GMap.size s1 : Int) = W64 0) =
        decide (GMap.size s0 = 1 ∧ GMap.size s1 = 0) from by
      apply decide_eq_decide.2
      constructor
      · intro h; exact ⟨by word, by word⟩
      · intro h; rw [h.2]; rfl]
    iapply HΦ
    iframe
  · ihave Htrk := Htrkback $$ Hvf
    rw [show decide (GMap.size s0 = 1 ∧ GMap.size s1 = 0) = false from by
      apply decide_eq_false
      intro h; apply Hif; rw [h.1]; rfl]
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
