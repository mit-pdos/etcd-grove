/-
Port of `election_proof/proof_Progress__ResetState.v`.
-/
import EtcdGrove.Raft.Spec.Progress__ResetState
import EtcdGrove.Raft.Spec.Inflights__reset

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

theorem tracker.Progress.ResetState.wp_proof
    (wp_Inflights_reset : tracker.Inflights.reset.spec (GF := GF) (hG := hG)) :
    tracker.Progress.ResetState.spec (GF := GF) (hG := hG) := by
  intro pr p st
  wp_start as Hpr
  iNamed Hpr
  wp_auto
  wp_apply wp_Inflights_reset $$ [$Hinfl] as Hinfl
  iapply HΦ
  iapply ownProgress_intro pr _ (progressResetState p st) $$ Hpv [Hinfl]
  · dsimp only [progressResetState]
    iexact Hinfl
  ipureintro
  obtain ⟨h1, h2, h3, h4, h5, h6, h8, h9⟩ := (progressAbs_Some _ _ _).1 Habs
  apply (progressAbs_Some _ _ _).2
  exact ⟨h1, rfl, h3, h4, h5, rfl, rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
