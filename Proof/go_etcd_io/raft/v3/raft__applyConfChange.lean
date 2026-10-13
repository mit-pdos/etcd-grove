/- Lean-first (no Rocq counterpart), 2026-10-13: reconfiguration stage D. -/
module

public import Spec.go_etcd_io.raft.v3.raft__applyConfChange
public import Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__LeaveJoint
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__EnterJoint
public import Spec.go_etcd_io.raft.v3.confchange.Changer__Simple

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

/-- The struct opened at its tracker and log (`ownRaftPhys_retrack`); the `Changer` reads
the tracker (`ownTracker_toCC`) and the last index; `cc.LeaveJoint()` is false and
`cc.EnterJoint()` says not joint (`ccApplyM_noop`), so `Simple` runs, and answers the
configuration it started from; the old `Progress` objects' rings go to the new ones
(`ownResult_noop_transfer`), and `switchToConfig` installs them. The `LeaveJoint`/
`EnterJoint` methods of the `Changer` are unreachable. -/
theorem raft.applyConfChange.wp_proof
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_LeaveJoint : raftpb.ConfChangeV2.LeaveJoint.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_EnterJoint : raftpb.ConfChangeV2.EnterJoint.spec (GF := GF) (hG := hG))
    (wp_Changer_Simple : confchange.Changer.Simple.spec (GF := GF) (hG := hG))
    (wp_raft_switchToConfig : raft.switchToConfig.spec (GF := GF) (hG := hG)) :
    raft.applyConfChange.spec (GF := GF) (hG := hG) := by
  intro cfg r id s cc ccs dq lrn' Hd' Hsz' Hnoop
  have Hd : ∀ k, k ∈ domSet s.progress \ cfg → k ∉ cfg :=
    fun k hk => ((GMap.elem_of_difference _ _ _).1 hk).2
  obtain ⟨Hnl, ⟨al, Hej⟩, Hsimple⟩ := ccApplyM_simple cfg _ lrn' Hd _ _ Hnoop
  wp_start as H
  iNamed H
  icases ownRaftPhys_gh $$ Hphys with ⟨%Hgh, Hphys⟩
  icases ownRaftPhys_voter cfg r id s $$ Hphys with ⟨%Hv, Hphys⟩
  icases ownRaftPhys_retrack cfg cfg r id s Hv $$ Hphys with ⟨%tv, Htrkf, Htrk, Hlf, Hlog, Hback⟩
  icases ownTracker_toCC cfg tv ⟨s.votes, s.progress, s.prvals⟩ $$ Htrk
    with ⟨%pvs, Htc, HR, Hvotes, %Hfl, %Hmi, %Hsz⟩
  wp_auto
  wp_apply wp_raftLog_lastIndex $$ [$Hlog] as %li ⟨Hlog, -⟩
  wp_method_call
  wp_call
  wp_auto
  -- `cc.LeaveJoint()`: false
  wp_apply wp_ConfChangeV2_LeaveJoint cc ccs dq $$ [$Hccs] as Hccs
  rw [decide_eq_false Hnl]
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  -- `cc.EnterJoint()`: not joint
  wp_apply wp_ConfChangeV2_EnterJoint cc ccs dq $$ [$Hccs] as %rv ⟨Hccs, Hres⟩
  rw [Hej]
  icases Hres with %Hres
  subst Hres
  wp_auto
  -- `changer.Simple(cc.Changes...)`
  wp_apply wp_Changer_Simple _ { Tracker' := tv, LastIndex' := li }
      (cfgM cfg (domSet s.progress \ cfg)) s.progress pvs
      cc.Changes' ccs (DFrac.own 1) dq (DFrac.own 1) DFrac.discard (DFrac.own 1) Hmi
    $$ [$Hccs $Htc $changer]
    as %cfgv %trk %err ⟨-, Hccs, -, Hres⟩
  rw [show ({ cfg := cfgM cfg (domSet s.progress \ cfg), prs := flagsOf pvs } : CCState) =
      cfgState cfg (domSet s.progress \ cfg) by rw [Hfl]; rfl, Hsimple]
  simp only [ownResult]
  icases Hres with ⟨%Herr, Hc, Hw⟩
  subst Herr
  ihave Hc := (show ownCfgCC (GF := GF) cfgv (DFrac.own 1) (cfgState cfg lrn').cfg ⊢
    ownCfgCC cfgv (DFrac.own 1) (cfgM cfg lrn') from .rfl) $$ Hc
  ihave Hw := (show ownPrsW (GF := GF) { Tracker' := tv, LastIndex' := li } pvs trk
      (cfgState cfg lrn').prs ⊢
    ownPrsW { Tracker' := tv, LastIndex' := li } pvs trk (cfgFlags cfg lrn') from .rfl) $$ Hw
  imod ownResult_noop_transfer cfg lrn' Hd' _ pvs s.prvals cfgv trk Hsz' $$ [$Hc $Hw $HR]
    with ⟨%prs', %pvs', Hnew, %Hmk, %Hpd⟩
  wp_auto
  -- `r.switchToConfig(cfg, trk)`
  ihave Hback' : (∀ tv' prs'' pvs'', r.[raft, go!"trk"] ↦ tv' -∗
      ownTracker cfg tv' ⟨s.votes, prs'', pvs''⟩ -∗
      ownRaftPhys (GF := GF) cfg r id { s with progress := prs'', prvals := pvs'' })
      $$ [Hback Hlf Hlog]
  · iintro %tv' %prs'' %pvs'' Hf Ht
    ihave H := Hback $$ %tv' %s.votes %prs'' %pvs'' %s.logst Hlf Hf Ht Hlog %Hgh
    iapply ownRaftPhys_eq cfg r id _ _ (by cases s; rfl) $$ H
  wp_apply wp_raft_switchToConfig cfg r id s tv cfgv trk prs' pvs'
      (fun hl => ⟨Hv (by rw [hl]; decide), Hmk⟩) $$ [$Htrkf $Hback' $Hvotes $Hnew]
    as %cs %xs %ls %s' ⟨Hphys, Hcs, Hls, %Hcs0, %Hsw⟩
  · ipureintro; exact Hmi
  try wp_auto
  iapply HΦ $$ %cs %xs %ls %s'
  iframe Hphys Hccs Hcs Hls
  ipureintro
  have Hpd' : domSet prs' \ cfg = lrn' := by
    rw [Hpd]
    apply GMap.set_eq; intro k
    simp only [GMap.elem_of_difference, GMap.elem_of_union]
    constructor
    · rintro ⟨h | h, h'⟩
      · exact absurd h h'
      · exact h
    · intro h; exact ⟨.inr h, Hd' k h⟩
  refine ⟨⟨Hcs0.1, Hpd' ▸ Hcs0.2.1, Hcs0.2.2⟩, prs', pvs', fun _ => Hmk, Hsw⟩

end proof

end EtcdGrove
end Perennial
