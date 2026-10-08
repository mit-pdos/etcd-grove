/- Port of election_proof/proof_ProgressTracker__Committed.v. -/
import EtcdGrove.Raft.Spec.ProgressTracker__Committed
import EtcdGrove.Raft.Spec.JointConfig__CommittedIndex
import EtcdGrove.Raft.Spec.matchAckIndexer__AckedIndex

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
  wp_alloc p_ptr as p; wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear p
  ihave #Hidx : isAckedIndexer
      (interface.mkOk tracker.matchAckIndexer.ty #tv.Progress')
      (ownProgressMap tv.Progress' prs pvs) (pvsAcked pvs) $$ []
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
  ihave HP : ownProgressMap tv.Progress' prs pvs $$ [Hprogs]
  · unfold ownProgressMap
    iframe Hprs Hprogs
  -- the `Voters` field's location, out of `trk ↦ tv`
  icases (tracker.ProgressTracker.ProgressTracker_access_load_Config trk tv (DFrac.own 1)).access_strict
    $$ Htrk with ⟨Hcfgf, Hback1⟩
  icases (tracker.Config.Config_access_load_Voters _ tv.Config' (DFrac.own 1)).access_strict
    $$ Hcfgf with ⟨Hvf, Hback2⟩
  wp_apply wp_JointConfig_CommittedIndex _ _ voters_ref voters _ _ (pvsAcked pvs)
      $$ [$Hidx $HP $Hvf $Hvoters] as %N ⟨Hvf, ⟨%voters', %Hdom, Hvoters⟩, HP, %Hemp, %Hq⟩
  · ipureintro
    exact ⟨by rw [Hvoters_dom]; exact Hcfg_size, Hvoters_arr⟩
  wp_pures
  ihave Hcfgf := Hback2 $$ Hvf
  ihave Htrk := Hback1 $$ Hcfgf
  unfold ownProgressMap
  iNamed HP
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
