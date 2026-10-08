/-
Port of `election_proof/proof_Progress__IsPaused.v`.
-/
import EtcdGrove.Raft.Spec.Progress__IsPaused

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The three-armed switch; the `panic` arm is ruled out by the record's state being
one of the three (`progressAbs`, `Defs.lean`). `wp_auto` runs the switch: once the
state is a literal, the remaining tests are between closed `w64` literals. -/
theorem tracker.Progress.IsPaused.wp_proof :
    tracker.Progress.IsPaused.spec (GF := GF) (hG := hG) := by
  intro pr p
  wp_start as Hpr
  iNamed Hpr
  iNamed Hpr
  have Habs' := (progressAbs_Some _ _ _).1 Habs
  obtain ⟨-, Hst, -, -, -, -, -, Hpa, -⟩ := Habs'
  wp_auto
  unfold progressIsPaused
  cases h : p.state <;> rw [h] at Hst <;> simp only [prstateW64] at Hst <;>
    simp only [Hst] <;> wp_auto
  · -- StateProbe
    rw [Hpa]
    iapply HΦ
    iapply ownProgress_intro $$ Hpv Hinfl %Habs
  · -- StateReplicate
    rw [Hpa]
    iapply HΦ
    iapply ownProgress_intro $$ Hpv Hinfl %Habs
  · -- StateSnapshot: paused unconditionally
    iapply HΦ
    iapply ownProgress_intro $$ Hpv Hinfl %Habs

end proof

end EtcdGrove
end Perennial
