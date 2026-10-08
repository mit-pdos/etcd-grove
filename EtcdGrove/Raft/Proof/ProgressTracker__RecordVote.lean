/- Port of election_proof/proof_ProgressTracker__RecordVote.v. -/
import EtcdGrove.Raft.Spec.ProgressTracker__RecordVote

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
  intro cfg trk tv t src v
  obtain ⟨votes, prs, pvs⟩ := t
  dsimp only
  wp_start as ⟨Htrk, Hown⟩
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
    iapply ownTracker_intro (Hprs_dom := Hprs_dom) (Hvoters_arr := Hvoters_arr)
      (Hautoleave := Hautoleave) (Hvoters_dom := Hvoters_dom) (Hno_learners := Hno_learners)
      (Hcfg_size := Hcfg_size) (HmaxInfl := HmaxInfl) $$ Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext
  | none =>
    -- first vote from `src`
    simp only [Option.isSome_none, Bool.false_eq_true, decide_false, Bool.not_false]
    wp_auto
    wp_apply wp_mapInsert $$ [$Hvotes] as Hvotes
    iapply HΦ
    iframe Htrk
    simp only [recordVote, Hok]
    iapply ownTracker_intro (Hprs_dom := Hprs_dom) (Hvoters_arr := Hvoters_arr)
      (Hautoleave := Hautoleave) (Hvoters_dom := Hvoters_dom) (Hno_learners := Hno_learners)
      (Hcfg_size := Hcfg_size) (HmaxInfl := HmaxInfl) $$ Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext

end proof

end EtcdGrove
end Perennial
