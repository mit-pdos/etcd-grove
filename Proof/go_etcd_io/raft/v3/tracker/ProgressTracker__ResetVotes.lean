/-
Port of `election_proof/proof_ProgressTracker__ResetVotes.v`.
-/
module

public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__ResetVotes

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

/-- `ResetVotes` is `p.Votes = map[uint64]bool{}`: a fresh empty map, whose points-to
replaces the old one in the re-sealed tracker. -/
theorem tracker.ProgressTracker.ResetVotes.wp_proof :
    tracker.ProgressTracker.ResetVotes.spec (GF := GF) (hG := hG) := by
  intro c trk tv t
  wp_start as ⟨Htrk, Hown⟩
  iunfold ownTrackerC at Hown
  iNamed Hown
  wp_auto
  wp_apply wp_map_make1 (K := w64) (V := Bool) as %votesRef Hvotes_new
  iapply HΦ
  iframe Htrk
  iapply ownTrackerC_intro c { tv with Votes' := votesRef } ∅ t.prs t.peers Hinv Hdom Hflags Hsize
    HmaxInfl $$ Hvotes_new Hprs Hprogs Hcfg

end proof

end EtcdGrove
end Perennial
