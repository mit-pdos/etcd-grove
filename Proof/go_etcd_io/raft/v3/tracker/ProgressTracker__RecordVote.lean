/- Port of election_proof/proof_ProgressTracker__RecordVote.v. -/
module

public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__RecordVote

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

theorem tracker.ProgressTracker.RecordVote.wp_proof :
    tracker.ProgressTracker.RecordVote.spec (GF := GF) (hG := hG) := by
  intro c trk tv t src v
  obtain ⟨votes, prs, pvs⟩ := t
  dsimp only
  wp_start as ⟨Htrk, Hown⟩
  iunfold ownTrackerC at Hown
  iNamed Hown
  wp_auto
  wp_apply wp_map_lookup2 $$ [$Hvotes] as Hvotes
  cases Hok : votes !! src with
  | some v0 =>
    -- already voted: first write wins, the map is left alone
    simp only [Option.isSome_some, decide_true, Bool.not_true]
    wp_auto
    iapply HΦ
    iframe Htrk
    simp only [recordVote, Hok]
    iapply ownTrackerC_intro (Hinv := Hinv) (Hdom := Hdom) (Hflags := Hflags) (Hsize := Hsize)
      (HmaxInfl := HmaxInfl) $$ Hvotes Hprs Hprogs Hcfg
  | none =>
    -- first vote from `src`
    simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false]
    wp_auto
    wp_apply wp_mapInsert $$ [$Hvotes] as Hvotes
    iapply HΦ
    iframe Htrk
    simp only [recordVote, Hok]
    iapply ownTrackerC_intro (Hinv := Hinv) (Hdom := Hdom) (Hflags := Hflags) (Hsize := Hsize)
      (HmaxInfl := HmaxInfl) $$ Hvotes Hprs Hprogs Hcfg

end proof

end EtcdGrove
end Perennial
