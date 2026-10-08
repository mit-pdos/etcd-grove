/-
Port of election_proof/proof_Progress__SentCommit.v.
-/
import EtcdGrove.Raft.Spec.Progress__SentCommit

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
theorem tracker.Progress.SentCommit.wp_proof :
    tracker.Progress.SentCommit.spec (GF := GF) (hG := hG) := by
  intro pr p commit
  wp_start as Hpr
  iunfold ownProgress at Hpr
  icases Hpr with ⟨%pv, Hpr⟩
  iNamed Hpr
  wp_alloc pr_ptr as pr; wp_pures; wp_alloc commit_ptr as commit; wp_pures; wp_load; wp_pures
  wp_load; wp_pures; wp_store; wp_pures; iclear pr commit
  iapply HΦ
  iapply ownProgress_intro pr _ (progressSentCommit p commit) $$ Hpv [Hinfl]
  · dsimp only [progressSentCommit]
    iexact Hinfl
  ipureintro
  have H := (progressAbs_Some _ _ _).1 Habs
  apply (progressAbs_Some _ _ _).2
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := H
  exact ⟨h1, h2, h3, h4, rfl, h6, h7, h8, h9⟩

end proof

end EtcdGrove
end Perennial
