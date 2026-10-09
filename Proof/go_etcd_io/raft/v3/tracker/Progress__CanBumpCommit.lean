/- Port of election_proof/proof_Progress__CanBumpCommit.v. -/
module

public import Spec.go_etcd_io.raft.v3.tracker.Progress__CanBumpCommit

@[expose] public section

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

/-- Goose's `&&` short-circuits, so the second comparison is only evaluated when the
first holds; each arm is one `decide`. -/
theorem tracker.Progress.CanBumpCommit.wp_proof :
    tracker.Progress.CanBumpCommit.spec (GF := GF) (hG := hG) := by
  intro pr p index
  wp_start as H
  iNamed H
  unfold ownProgress
  iNamed Hpr
  have Habs' := (progressAbs_Some _ _ _).1 Habs
  obtain ⟨Hl, Hst, Hm, Hn, Hsc, -, -, -, -⟩ := Habs'
  wp_auto
  wp_if_destruct
  · rw [show decide (uint.Z pv.sentCommit' < uint.Z (pv.Next' - W64 1)) =
        progressCanBumpCommit p index by
      simp only [progressCanBumpCommit, ← Hsc, ← Hn, decide_eq_decide]
      exact ⟨fun h => ⟨Hif, h⟩, fun h => h.2⟩]
    iapply HΦ
    iexists pv
    iframe Hpv Hinfl
    ipureintro
    exact Habs
  · rw [show false = progressCanBumpCommit p index by
      simp only [progressCanBumpCommit, ← Hsc]
      simp only [Hif, false_and, decide_false]]
    iapply HΦ
    iexists pv
    iframe Hpv Hinfl
    ipureintro
    exact Habs

end proof

end EtcdGrove
end Perennial
