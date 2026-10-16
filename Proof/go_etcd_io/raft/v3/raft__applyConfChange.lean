/- Lean-first (no Rocq counterpart), 2026-10-13: reconfiguration stage D.

raft v3.7 (stage R4): `cc` is a `*pb.ConfChangeV2` (`ownCCV2`), read by `LeaveJoint`/`EnterJoint`
(pointer methods with specs, no longer unfolded); `cc.Changes...` opens it for the field load and
folds it back after the changer. -/
module

public import Spec.go_etcd_io.raft.v3.raft__applyConfChange
public import Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__LeaveJoint
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__EnterJoint
public import Spec.go_etcd_io.raft.v3.confchange.Changer__Simple
public import Spec.go_etcd_io.raft.v3.confchange.Changer__LeaveJoint
public import Spec.go_etcd_io.raft.v3.confchange.Changer__EnterJoint

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

/-- The struct opened at its tracker and log (`ownRaftPhysC_retrack`, with `Hvoter` at the new
voters and the node itself, as `switchToConfig` takes it); the `Changer` reads the tracker
(`ownTrackerC_toCC`: the state `cfgStateC c`, reachable) and the last index; `cc.LeaveJoint()`
and `cc.EnterJoint()` choose `LeaveJoint`, `EnterJoint` or `Simple` as `ccApplyM` does; the
result is reachable (`ccApplyM_good`) and passes `checkInvariants` (`ccApplyM_inv`), so with
the old objects' rings moved to the new ones it is an `ownConfigC` (`ownResult_transfer`);
`switchToConfig` installs it. -/
theorem raft.applyConfChange.wp_proof
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_LeaveJoint : raftpb.ConfChangeV2.LeaveJoint.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_EnterJoint : raftpb.ConfChangeV2.EnterJoint.spec (GF := GF) (hG := hG))
    (wp_Changer_LeaveJoint : confchange.Changer.LeaveJoint.spec (GF := GF) (hG := hG))
    (wp_Changer_EnterJoint : confchange.Changer.EnterJoint.spec (GF := GF) (hG := hG))
    (wp_Changer_Simple : confchange.Changer.Simple.spec (GF := GF) (hG := hG))
    (wp_raft_switchToConfig : raft.switchToConfig.spec (GF := GF) (hG := hG)) :
    raft.applyConfChange.spec (GF := GF) (hG := hG) := by
  intro c r id s cc ccm dq c' Happ0 Hsz Hcand
  wp_start as H
  iNamed H
  icases ownRaftPhysC_gh c r id s $$ Hphys with ⟨%Hgh, Hphys⟩
  -- (stage R8a) the leader's progress bound of the old values, for the new ones (`PrKept`)
  icases ownRaftPhysC_prvals_ok c r id s $$ Hphys with ⟨%Hok0, -, Hphys⟩
  icases ownRaftPhysC_retrack c'.cfg c c.voters (c'.cfg.voters ∪ {[id]}) r id s
      (fun _ => GMap.elem_of_union_r _ (GMap.elem_of_singleton_2 id)) $$ Hphys
    with ⟨%tv, Htrkf, Htrk, Hlf, Hlog, Hback⟩
  icases ownTrackerC_toCC c tv ⟨s.votes, s.progress, s.prvals⟩ $$ Htrk
    with ⟨%pvs, Htc, HR, Hvotes, %Hfl, %Hmi, %Hg⟩
  obtain ⟨Hgood, -, -, -⟩ := Hg
  have Hst : ({ cfg := c, prs := flagsOf pvs } : CCState) = cfgStateC c := by
    rw [Hfl]; unfold cfgStateC; rw [← Hgood.flags]
  have Hgood' : CCGood (cfgStateC c) := by
    have h := Hgood
    unfold cfgStateC; rw [← Hgood.flags]; exact h
  have Happ := Happ0
  unfold ccApplyM at Happ
  wp_auto
  wp_apply wp_raftLog_lastIndex $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
  have Hli' : li = logLast s.logst := logLast_eq_of_Z _ _ Hli
  wp_apply wp_ConfChangeV2_LeaveJoint cc dq ccm $$ [$Hcc] as Hcc
  by_cases Hlj : ccm.transition = W32 0 ∧ ccm.changes = []
  · -- `changer.LeaveJoint()`
    rw [decide_eq_true Hlj]
    rw [ite_eq_left Hlj] at Happ
    wp_auto
    wp_apply wp_Changer_LeaveJoint _ { Tracker' := tv, LastIndex' := li } c s.progress pvs
        (DFrac.own 1) (DFrac.own 1) DFrac.discard (DFrac.own 1)
      $$ [$Htc $changer]
      as %cfgv %trk %err ⟨-, -, Hres⟩
    rw [Hst, Happ]
    simp only [ownResult]
    icases Hres with ⟨%Herr, Hc, Hw⟩
    subst Herr
    imod ownResult_transfer c' (ccApplyM_good Hgood' _ _ Happ0) (ccApplyM_inv _ _ Happ0) _ pvs
        s.prvals cfgv trk Hsz $$ [$Hc $Hw $HR]
      with ⟨%prs', %pvs', Hnew, %Hmk, %Hpk, %Hpd⟩
    wp_auto
    -- `r.switchToConfig(cfg, trk)`
    ihave Hback' : (∀ tv' prs'' pvs'', r.[raft, go!"trk"] ↦ tv' -∗
        ownTrackerC c'.cfg tv' ⟨s.votes, prs'', pvs''⟩ -∗
        ⌜PrvalsOk { s with progress := prs'', prvals := pvs'' }⌝ -∗
        ownRaftPhysCV (GF := GF) c'.cfg (c'.cfg.voters ∪ {[id]}) r id
          { s with progress := prs'', prvals := pvs'' })
        $$ [Hback Hlf Hlog]
    · iintro %tv' %prs'' %pvs'' Hf Ht %Hok
      ihave H := Hback $$ %tv' %s.votes %prs'' %pvs'' %s.logst Hlf Hf Ht Hlog %Hgh
        %(Hok.of_fields rfl rfl rfl)
      iapply ownRaftPhysC_eq c'.cfg r id _ _ (by cases s; rfl) $$ H
    wp_apply wp_raft_switchToConfig c'.cfg r id s tv cfgv trk prs' pvs'
        (fun hl => by
          by_cases hin : id ∈ c'.cfg.voters
          · exact .inl ⟨hin, Hmk⟩
          · exact .inr hin) Hcand
        (fun hl => by
          simp only at Hpk; rw [Hli'] at Hpk
          exact Hpk.prOk (fun v p hv => Hok0.lookup hl hv))
      $$ [$Htrkf $Hback' $Hvotes $Hnew]
      as %cs %xs %os %ls %lns %s' ⟨Hphys, Hcs, %Hcs0, %Hsw⟩
    · ipureintro; exact Hmi
    try wp_auto
    iapply HΦ $$ %cs %xs %os %ls %lns %s'
    iframe Hphys Hcc Hcs
    ipureintro
    exact ⟨Hcs0, prs', pvs', Hpd, Hmk, Hsw⟩
  · rw [decide_eq_false Hlj]
    rw [ite_eq_right Hlj] at Happ
    wp_auto
    wp_apply wp_ConfChangeV2_EnterJoint cc dq ccm
      (fun Hn => by rw [Hn] at Happ; cases Happ) $$ [$Hcc] as %rv ⟨Hcc, Hres⟩
    cases Hej : enterJointOf ccm.transition ccm.changes.length with
    | none => rw [Hej] at Happ; cases Happ
    | some p =>
      obtain ⟨al, ok⟩ := p
      rw [Hej] at Happ
      icases Hres with %Hres
      subst Hres
      cases ok
      · -- `changer.Simple(cc.Changes...)`
        simp only at Happ
        iunfold ownCCV2 at Hcc
        icases Hcc with ⟨%pt, %chs, %ls, %cs, %uf, %Hnn, HT0, #cT, HCh, Hch, #Hccs, HC0, #Hcs, #Hpb⟩
        wp_auto
        wp_apply wp_Changer_Simple _ { Tracker' := tv, LastIndex' := li } c s.progress pvs
            chs ls ccm.changes (DFrac.own 1) dq (DFrac.own 1) DFrac.discard (DFrac.own 1) Hmi
          $$ [$Hch $Htc $changer]
          as %cfgv %trk %err ⟨-, Hch, -, Hres⟩
        · iexact Hccs
        ihave Hcc : ownCCV2 cc dq ccm $$ [HT0 HCh Hch HC0]
        · iunfold ownCCV2
          iexists pt, chs, ls, cs, uf
          iframe
          iframe cT Hccs Hcs Hpb
          ipureintro; exact Hnn
        rw [Hst, Happ]
        simp only [ownResult]
        icases Hres with ⟨%Herr, Hc, Hw⟩
        subst Herr
        imod ownResult_transfer c' (ccApplyM_good Hgood' _ _ Happ0) (ccApplyM_inv _ _ Happ0) _ pvs
            s.prvals cfgv trk Hsz $$ [$Hc $Hw $HR]
          with ⟨%prs', %pvs', Hnew, %Hmk, %Hpk, %Hpd⟩
        wp_auto
        -- `r.switchToConfig(cfg, trk)`
        ihave Hback' : (∀ tv' prs'' pvs'', r.[raft, go!"trk"] ↦ tv' -∗
            ownTrackerC c'.cfg tv' ⟨s.votes, prs'', pvs''⟩ -∗
            ⌜PrvalsOk { s with progress := prs'', prvals := pvs'' }⌝ -∗
            ownRaftPhysCV (GF := GF) c'.cfg (c'.cfg.voters ∪ {[id]}) r id
              { s with progress := prs'', prvals := pvs'' })
            $$ [Hback Hlf Hlog]
        · iintro %tv' %prs'' %pvs'' Hf Ht %Hok
          ihave H := Hback $$ %tv' %s.votes %prs'' %pvs'' %s.logst Hlf Hf Ht Hlog %Hgh
            %(Hok.of_fields rfl rfl rfl)
          iapply ownRaftPhysC_eq c'.cfg r id _ _ (by cases s; rfl) $$ H
        wp_apply wp_raft_switchToConfig c'.cfg r id s tv cfgv trk prs' pvs'
            (fun hl => by
              by_cases hin : id ∈ c'.cfg.voters
              · exact .inl ⟨hin, Hmk⟩
              · exact .inr hin) Hcand
            (fun hl => by
              simp only at Hpk; rw [Hli'] at Hpk
              exact Hpk.prOk (fun v p hv => Hok0.lookup hl hv))
          $$ [$Htrkf $Hback' $Hvotes $Hnew]
          as %cs %xs %os %ls %lns %s' ⟨Hphys, Hcs, %Hcs0, %Hsw⟩
        · ipureintro; exact Hmi
        try wp_auto
        iapply HΦ $$ %cs %xs %os %ls %lns %s'
        iframe Hphys Hcc Hcs
        ipureintro
        exact ⟨Hcs0, prs', pvs', Hpd, Hmk, Hsw⟩
      · -- `changer.EnterJoint(autoLeave, cc.Changes...)`
        simp only at Happ
        iunfold ownCCV2 at Hcc
        icases Hcc with ⟨%pt, %chs, %ls, %cs, %uf, %Hnn, HT0, #cT, HCh, Hch, #Hccs, HC0, #Hcs, #Hpb⟩
        wp_auto
        wp_apply wp_Changer_EnterJoint _ { Tracker' := tv, LastIndex' := li } c s.progress pvs al
            chs ls ccm.changes (DFrac.own 1) dq (DFrac.own 1) DFrac.discard (DFrac.own 1) Hmi
          $$ [$Hch $Htc $changer]
          as %cfgv %trk %err ⟨-, Hch, -, Hres⟩
        · iexact Hccs
        ihave Hcc : ownCCV2 cc dq ccm $$ [HT0 HCh Hch HC0]
        · iunfold ownCCV2
          iexists pt, chs, ls, cs, uf
          iframe
          iframe cT Hccs Hcs Hpb
          ipureintro; exact Hnn
        rw [Hst, Happ]
        simp only [ownResult]
        icases Hres with ⟨%Herr, Hc, Hw⟩
        subst Herr
        imod ownResult_transfer c' (ccApplyM_good Hgood' _ _ Happ0) (ccApplyM_inv _ _ Happ0) _ pvs
            s.prvals cfgv trk Hsz $$ [$Hc $Hw $HR]
          with ⟨%prs', %pvs', Hnew, %Hmk, %Hpk, %Hpd⟩
        wp_auto
        -- `r.switchToConfig(cfg, trk)`
        ihave Hback' : (∀ tv' prs'' pvs'', r.[raft, go!"trk"] ↦ tv' -∗
            ownTrackerC c'.cfg tv' ⟨s.votes, prs'', pvs''⟩ -∗
            ⌜PrvalsOk { s with progress := prs'', prvals := pvs'' }⌝ -∗
            ownRaftPhysCV (GF := GF) c'.cfg (c'.cfg.voters ∪ {[id]}) r id
              { s with progress := prs'', prvals := pvs'' })
            $$ [Hback Hlf Hlog]
        · iintro %tv' %prs'' %pvs'' Hf Ht %Hok
          ihave H := Hback $$ %tv' %s.votes %prs'' %pvs'' %s.logst Hlf Hf Ht Hlog %Hgh
            %(Hok.of_fields rfl rfl rfl)
          iapply ownRaftPhysC_eq c'.cfg r id _ _ (by cases s; rfl) $$ H
        wp_apply wp_raft_switchToConfig c'.cfg r id s tv cfgv trk prs' pvs'
            (fun hl => by
              by_cases hin : id ∈ c'.cfg.voters
              · exact .inl ⟨hin, Hmk⟩
              · exact .inr hin) Hcand
            (fun hl => by
              simp only at Hpk; rw [Hli'] at Hpk
              exact Hpk.prOk (fun v p hv => Hok0.lookup hl hv))
          $$ [$Htrkf $Hback' $Hvotes $Hnew]
          as %cs %xs %os %ls %lns %s' ⟨Hphys, Hcs, %Hcs0, %Hsw⟩
        · ipureintro; exact Hmi
        try wp_auto
        iapply HΦ $$ %cs %xs %os %ls %lns %s'
        iframe Hphys Hcc Hcs
        ipureintro
        exact ⟨Hcs0, prs', pvs', Hpd, Hmk, Hsw⟩

end proof

end EtcdGrove
end Perennial
