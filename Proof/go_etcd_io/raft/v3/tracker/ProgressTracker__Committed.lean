/- Port of election_proof/proof_ProgressTracker__Committed.v. -/
module

public import Spec.go_etcd_io.raft.v3.tracker.ProgressTracker__Committed
public import Spec.go_etcd_io.raft.v3.quorum.JointConfig__CommittedIndex
public import Spec.go_etcd_io.raft.v3.tracker.matchAckIndexer__AckedIndex

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

/-- Open `ownTracker`; load `p.Voters` (the array value) and hand it to
`JointConfig.CommittedIndex` with the voter map and the progress map with its
`Progress` objects (`ownProgressMap`) as the indexer's resource -- the indexer is
`matchAckIndexer(p.Progress)`, whose contract comes from `matchAckIndexer.AckedIndex`'s
triple -- then close `ownTracker` again around the voter map it hands back. -/
theorem tracker.ProgressTracker.Committed.wp_proof
    (wp_JointConfig_CommittedIndex : quorum.JointConfig.CommittedIndex.spec (GF := GF) (hG := hG))
    (wp_matchAckIndexer_AckedIndex :
      tracker.matchAckIndexer.AckedIndex.spec (GF := GF) (hG := hG)) :
    tracker.ProgressTracker.Committed.spec (GF := GF) (hG := hG) := by
  intro cfg trk tv t
  obtain ⟨votes, prs, pvs⟩ := t
  wp_start as ⟨Htrk, Hown⟩
  unfold ownTracker
  iNamed Hown
  simp only at *
  wp_auto
  ihave #Hidx : isAckedIndexer
      (interface.mkOk tracker.matchAckIndexer.ty #tv.Progress')
      (ownProgressMap tv.Progress' pvs) (pvsAcked pvs) $$ []
  · unfold isAckedIndexer
    iexists _
    isplitr
    · ipureintro; rfl
    imodintro
    iintro %id %Ψ
    imodintro
    iintro HP HΨ
    wp_apply wp_matchAckIndexer_AckedIndex $$ [$HP] as HP
    iapply HΨ $$ HP
  ihave HP : ownProgressMap tv.Progress' pvs $$ [Hprogs]
  · unfold ownProgressMap
    iexists prs
    iframe Hprs Hprogs
  -- `p.Voters` was read out of `trk ↦ tv` when the method value was formed
  wp_apply wp_JointConfig_CommittedIndex _ voters_ref voters _ _ (pvsAcked pvs)
      $$ [$Hidx $HP $Hvoters] as %N ⟨⟨%voters', %Hdom, Hvoters⟩, HP, %Hemp, %Hq⟩
  · ipureintro
    exact ⟨by rw [Hvoters_dom]; exact Hcfg_size, Hvoters_arr⟩
  -- the map is the tracker's: its contents agree with `Hprs`
  iunfold ownProgressMap at HP
  icases HP with ⟨%prs', #Hprs', Hprogs⟩
  ihave %Hprs_eq := progress_map_agree _ _ _ _ _ $$ Hprs Hprs'
  subst Hprs_eq
  iapply HΦ
  iframe Htrk
  rw [Hvoters_dom] at Hemp Hq
  isplitl [Hvotes Hlearners HlearnersNext Hvoters Hprogs]
  · iexists voters_ref, voters', learners, learnersNext
    simp only [named]
    iframe Hvotes Hprs Hprogs Hvoters Hlearners HlearnersNext
    ipureintro
    exact ⟨Hprs_dom, Hvoters_arr, Hautoleave, by rw [Hdom]; exact Hvoters_dom, Hno_learners,
      Hcfg_size, HmaxInfl⟩
  ipureintro
  exact ⟨Hemp, Hq⟩

end proof

end EtcdGrove
end Perennial
