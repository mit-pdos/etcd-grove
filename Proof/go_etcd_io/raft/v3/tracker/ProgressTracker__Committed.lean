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

/-- Open `ownTrackerC`; hand `&p.Config.Voters` to `JointConfig.CommittedIndex` with the two
voter halves (`ownCfgCC_voters`) and the progress map with its `Progress` objects
(`ownProgressMap`) as the indexer's resource -- the indexer is `matchAckIndexer(p.Progress)`,
whose contract comes from `matchAckIndexer.AckedIndex`'s triple -- then close `ownTrackerC`
again. -/
theorem tracker.ProgressTracker.Committed.wp_proof
    (wp_JointConfig_CommittedIndex : quorum.JointConfig.CommittedIndex.spec (GF := GF) (hG := hG))
    (wp_matchAckIndexer_AckedIndex :
      tracker.matchAckIndexer.AckedIndex.spec (GF := GF) (hG := hG)) :
    tracker.ProgressTracker.Committed.spec (GF := GF) (hG := hG) := by
  intro c trk tv t
  obtain ⟨votes, prs, pvs⟩ := t
  wp_start as ⟨Htrk, Hown⟩
  iunfold ownTrackerC at Hown
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
  icases ownCfgCC_voters _ _ $$ Hcfg with ⟨%vin, %vout, %Harr, Hv0, Hv1, Hcback⟩
  have Hsz0 : (GMap.size c.incoming : Int) ≤ 2 ^ 62 := by
    have := size_le_of_sub_dom c.incoming prs (by
      rw [Hdom]; exact incoming_sub_ids c)
    omega
  have Hsz1 : (GMap.size c.outgoing : Int) ≤ 2 ^ 62 := by
    have := size_le_of_sub_dom c.outgoing prs (by
      rw [Hdom]; exact outgoing_sub_ids c)
    omega
  -- the `Voters` field's location, out of `trk ↦ tv`
  icases (tracker.ProgressTracker.ProgressTracker_access_load_Config trk tv (DFrac.own 1)).access_strict
    $$ Htrk with ⟨Hcfgf, Hback1⟩
  icases (tracker.Config.Config_access_load_Voters _ tv.Config' (DFrac.own 1)).access_strict
    $$ Hcfgf with ⟨Hvf, Hback2⟩
  wp_apply wp_JointConfig_CommittedIndex _ (DFrac.own 1) _ vin vout c.incoming c.outgoing _ _
      (pvsAcked pvs) Harr Hsz0 Hsz1 $$ [$Hidx $HP $Hvf $Hv0 $Hv1] as %N ⟨Hvf, Hv0, Hv1, HP, %HN⟩
  ihave Hcfgf := Hback2 $$ Hvf
  ihave Htrk := Hback1 $$ Hcfgf
  ihave Hcfg := Hcback $$ Hv0 Hv1
  -- the map is the tracker's: its contents agree with `Hprs`
  iunfold ownProgressMap at HP
  icases HP with ⟨%prs', #Hprs', Hprogs⟩
  ihave %Hprs_eq := progress_map_agree _ _ _ _ _ $$ Hprs Hprs'
  subst Hprs_eq
  iapply HΦ
  iframe Htrk
  isplitl [Hvotes Hprogs Hcfg]
  · iapply ownTrackerC_intro c tv votes prs pvs Hinv Hdom Hflags Hsize HmaxInfl
      $$ Hvotes Hprs Hprogs Hcfg
  ipureintro
  exact HN

end proof

end EtcdGrove
end Perennial
