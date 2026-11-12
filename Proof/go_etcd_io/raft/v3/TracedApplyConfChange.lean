/-
Lean-first (no Rocq counterpart). Trace-check, step 4 (2026-11-12; `notes/trace-check-design.md`, "Step
4", the `confc` row; §3.4) and step 5 (2026-11-12, "Step 5"): **`r.applyConfChange(cc)` in both modes**,
proved from the code: `raft.applyConfChange.spec_proof` (the one proof; `raft.applyConfChange.wp_proof` is
it), the struct opened at its tracker *and* at its header and log (`ownRaftPhysCV_reconfigCore`), the
`Changer`'s given-back old configuration lent to `switchToConfig`'s hook (traced) with its size, and the
caller's gate fired by the one `switchToConfig.spec`. Its instances: step 4's `hCC`
(`raft.applyConfChange.tracedSpec_of_spec`: the gate from `trCapB_hookGate_applyCC` traced, from the nil
logger untraced, the capability moved to the end state through `ApplyCCOkC`'s follower arm), and the old
untraced statement from `hCC` (`raft.applyConfChange.specU_of_tracedSpec`, `run`'s static arm).
Raft-internal.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRunSpecs
public import Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__LeaveJoint
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__EnterJoint
public import Spec.go_etcd_io.raft.v3.confchange.Changer__Simple
public import Spec.go_etcd_io.raft.v3.confchange.Changer__LeaveJoint
public import Spec.go_etcd_io.raft.v3.confchange.Changer__EnterJoint
public import Spec.go_etcd_io.raft.v3.raft__switchToConfig
public import Proof.go_etcd_io.raft.v3.TracedApplyCC

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The old untraced statement from `hCC`** (`run`'s static `confc` arm): the capability `emp`, the
gated premises vacuous; the names `raftNames0`, which the capability does not read untraced. -/
theorem raft.applyConfChange.specU_of_tracedSpec
    (h : raft.applyConfChange.tracedSpec (GF := GF) (hG := hG)) :
    raft.applyConfChange.specU (GF := GF) (hG := hG) := by
  intro c r id s cc ccm dq c' Happ Hsz Hltz Hcand Hli2 Htr
  iintro %Φ ⟨#Hpkg, Hphys, Hcc⟩ HΦ
  iapply h c r id s cc ccm dq c' raftNames0 Happ Hsz Hltz Hcand Hli2 (fun hn => absurd Htr hn)
    $$ [$Hpkg $Hphys $Hcc]
  · rw [Htr]; simp only [trCapB]; iempintro
  inext
  iintro %cs %xs %os %ls %lns %s' ⟨H1, H2, H3, %H4, %H5, -⟩
  iapply HΦ $$ %cs %xs %os %ls %lns %s'
  iframe H1 H2 H3
  ipureintro; exact ⟨H4, H5⟩

/-- A follower's `applyConfChange` keeps the protocol reading (`ApplyCCOkC`'s non-leader arm). -/
private theorem applyCC_follower_pstate {c' : CfgM} {id : w64} {s s' : NState}
    (hf : s.role = .follower) (H : ApplyCCOkC c' id s s') : toPState s = toPState s' := by
  obtain ⟨prs, pvs, -, -, Hsw⟩ := H
  unfold SwitchOkC at Hsw
  rw [ite_eq_right (show ¬ ({ s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } :
    NState).role = .leader by simp [hf])] at Hsw
  subst Hsw; simp [toPState, hf]

/-- **Step 4's `hCC` from the one proof**: traced, the gate from the capability
(`trCapB_hookGate_applyCC` at `c'.cfg = c`), the capability moved to the end state (a follower keeps
`toPState`, `simIdle_congr`); untraced, the gate from the struct's nil logger, the capability `emp`. -/
theorem raft.applyConfChange.tracedSpec_of_spec (h : raft.applyConfChange.spec (GF := GF) (hG := hG)) :
    raft.applyConfChange.tracedSpec (GF := GF) (hG := hG) := by
  intro c r id s cc ccm dq c' γ Happ Hsz Hltz Hcand Hli2 Htrg
  iintro %Φ ⟨#Hpkg, Hphys, Hcc, Hcap⟩ HΦ
  icases ownRaftPhysC_traceLoggerG _ _ _ _ _ $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  cases htr : s.gh.tr with
  | none =>
    iapply h c r id s cc ccm dq c' iprop(emp) Happ Hsz Hltz Hcand Hli2 (fun hn => absurd htr hn)
      $$ [$Hpkg $Hphys $Hcc]
    · rw [htr]
      iapply hookGate_none r _ tl iprop(emp) (Htlok htr)
      iframe Htl
    inext
    iintro %cs %xs %os %ls %lns %s' ⟨H1, H2, H3, %H4, %H5, -⟩
    iapply HΦ $$ %cs %xs %os %ls %lns %s'
    iframe H1 H2 H3
    isplitr
    · ipureintro; exact H4
    isplitr
    · ipureintro; exact H5
    simp only [trCapB]; iempintro
  | some γd =>
    obtain ⟨hf, hc, hboot, hcl, hb1, hb2, hb3⟩ := Htrg (by rw [htr]; simp)
    have Hs : s.gh.tr.isSome → s.gh.tr ≠ none := fun h hn => by rw [hn] at h; cases h
    ihave Hgate := trCapB_hookGate_applyCC s.gh.tr γ r id c c'.cfg tl s (fun _ => True) (fun _ => True)
      (fun _ _ => trivial) (fun _ => hboot) (fun _ => hcl) (by rw [hc]; exact Nat.le_refl _) (fun _ => ⟨hb1, hb2, hb3⟩) Htlok
      $$ [$Htl Hcap]
    · rw [htr]; iexact Hcap
    iapply h c r id s cc ccm dq c' _ Happ Hsz Hltz Hcand Hli2 (fun _ => hf) $$ [$Hpkg $Hphys $Hcc $Hgate]
    inext
    iintro %cs %xs %os %ls %lns %s' ⟨H1, H2, H3, %H4, %H5, Hcap⟩
    iapply HΦ $$ %cs %xs %os %ls %lns %s'
    iframe H1 H2 H3
    isplitr
    · ipureintro; exact H4
    isplitr
    · ipureintro; exact H5
    have hp := applyCC_follower_pstate hf H5
    have e : (fun C => SimIdle C s) = (fun C => SimIdle C s') := funext (simIdle_congr hp)
    rw [hc, ← e]
    iExactEq Hcap; rw [htr]

/-- **`r.applyConfChange(cc)`, both modes, from the code** (the one proof). -/
theorem raft.applyConfChange.spec_proof
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_LeaveJoint : raftpb.ConfChangeV2.LeaveJoint.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_EnterJoint : raftpb.ConfChangeV2.EnterJoint.spec (GF := GF) (hG := hG))
    (wp_Changer_LeaveJoint : confchange.Changer.LeaveJoint.spec (GF := GF) (hG := hG))
    (wp_Changer_EnterJoint : confchange.Changer.EnterJoint.spec (GF := GF) (hG := hG))
    (wp_Changer_Simple : confchange.Changer.Simple.spec (GF := GF) (hG := hG))
    (wp_raft_switchToConfig : raft.switchToConfig.spec (GF := GF) (hG := hG)) :
    raft.applyConfChange.spec (GF := GF) (hG := hG) := by
  intro c r id s cc ccm dq c' Q Happ0 Hsz Hltz Hcand Hli2 Htrg
  wp_start as H
  iNamed H
  iunfold HookGate at Hgate
  imod Hgate with ⟨%tl, #Htl, Hfire⟩
  -- (stage R8a) the leader's progress bound of the old values, for the new ones (`PrKept`)
  icases ownRaftPhysC_prvals_ok c r id s $$ Hphys with ⟨%Hok0, -, Hphys⟩
  icases ownRaftPhysCV_reconfigCore c c'.cfg c.voters (c'.cfg.voters ∪ {[id]}) r id s
      (fun _ _ => GMap.elem_of_union_r _ (GMap.elem_of_singleton_2 id)) $$ Hphys
    with ⟨%tv, Htrkf, Htrk, Hcore, Hback⟩
  icases ownTrackerC_pure c _ _ $$ Htrk with ⟨%Hpure, Htrk⟩
  have Hsz0 : CfgSizeOk c := by
    obtain ⟨-, Hdom, -, Hsize, -⟩ := Hpure
    simp only at Hdom Hsize
    constructor
    · have := size_le_of_sub_dom c.incoming s.progress (by rw [Hdom]; exact incoming_sub_ids c)
      omega
    · have := size_le_of_sub_dom c.outgoing s.progress (by rw [Hdom]; exact outgoing_sub_ids c)
      omega
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
  iunfold ownRaftCore at Hcore
  icases Hcore with ⟨#Hidf, HT, HV, HS, HL, Hlog⟩
  wp_auto
  wp_apply wp_raftLog_lastIndex $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
  ihave Hcore : ownRaftCore (GF := GF) r id s $$ [HT HV HS HL Hlog]
  · iunfold ownRaftCore; iframe; iframe Hidf
  have Hli' : li = logLast s.logst := logLast_eq_of_Z _ _ Hli
  have Hli2 : s.gh.ns = true → s.role = .leader → 2 ≤ uint.Z (logLast s.logst) := by
    intro hns hl
    have h := Hli2 hns hl
    unfold plogLastIndexZ at h
    rw [List.length_append] at h
    rw [← Hli', Hli]; push_cast at h; omega
  wp_apply wp_ConfChangeV2_LeaveJoint cc dq ccm $$ [$Hcc] as Hcc
  by_cases Hlj : ccm.transition = W32 0 ∧ ccm.changes = []
  · -- `changer.LeaveJoint()`
    rw [decide_eq_true Hlj]
    rw [ite_eq_left Hlj] at Happ
    wp_auto
    wp_apply wp_Changer_LeaveJoint _ { Tracker' := tv, LastIndex' := li } c s.progress pvs
        (DFrac.own 1) (DFrac.own 1) DFrac.discard (DFrac.own 1)
      $$ [$Htc $changer]
      as %cfgv %trk %err ⟨-, Hotc, Hres⟩
    rw [Hst, Happ]
    simp only [ownResult]
    icases Hres with ⟨%Herr, Hc, Hw⟩
    subst Herr
    imod ownResult_transfer c' (ccApplyM_good Hgood' _ _ Happ0) (ccApplyM_inv _ _ Happ0) _ pvs
        s.prvals cfgv trk Hsz $$ [$Hc $Hw $HR]
      with ⟨%prs', %pvs', Hnew, %Hmk, %Hpk, %Hpd⟩
    wp_auto
    -- `r.switchToConfig(cfg, trk)`
    iunfold ownTrackerCC at Hotc
    icases Hotc with ⟨Hocfg, -, -⟩
    ihave Hold : trOwn (GF := GF) s.gh.tr iprop(ownCfgCC tv.Config' (DFrac.own 1) c ∗ ⌜CfgSizeOk c⌝)
      $$ [Hocfg]
    · cases s.gh.tr
      · iclear Hocfg; simp only [trOwn]; iempintro
      · simp only [trOwn]; iframe Hocfg; ipureintro; exact Hsz0
    wp_apply wp_raft_switchToConfig c'.cfg r id s tv cfgv trk prs' pvs' tl c Q
        (fun _ _ => Hmk) Hltz Hcand
        (fun hl => by
          simp only at Hpk; rw [Hli'] at Hpk
          exact Hpk.prOkN (fun v p hv => Hok0.lookup hl hv) (fun hns => Hli2 hns hl))
      Htrg $$ [$Htrkf $Hcore $Hback $Hvotes $Hnew $Htl $Hold $Hfire]
      as %cs %xs %os %ls %lns %s' ⟨Hphys, Hcs, %Hcs0, %Hsw, Hcap⟩
    · ipureintro; exact Hmi
    try wp_auto
    iapply HΦ $$ %cs %xs %os %ls %lns %s'
    iframe Hphys Hcc Hcs Hcap
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
        iunfold ownConfChangeV2 at Hcc
        icases Hcc with ⟨%pt, %chs, %ls, %cs, %uf, %Hnn, HT0, #cT, HCh, Hch, #Hccs, HC0, #Hcs, #Hpb⟩
        wp_auto
        wp_apply wp_Changer_Simple _ { Tracker' := tv, LastIndex' := li } c s.progress pvs
            chs ls ccm.changes (DFrac.own 1) dq (DFrac.own 1) DFrac.discard (DFrac.own 1) Hmi
          $$ [$Hch $Htc $changer]
          as %cfgv %trk %err ⟨-, Hch, Hotc, Hres⟩
        · iexact Hccs
        ihave Hcc : ownConfChangeV2 cc dq ccm $$ [HT0 HCh Hch HC0]
        · iunfold ownConfChangeV2
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
        iunfold ownTrackerCC at Hotc
        icases Hotc with ⟨Hocfg, -, -⟩
        ihave Hold : trOwn (GF := GF) s.gh.tr iprop(ownCfgCC tv.Config' (DFrac.own 1) c ∗ ⌜CfgSizeOk c⌝)
          $$ [Hocfg]
        · cases s.gh.tr
          · iclear Hocfg; simp only [trOwn]; iempintro
          · simp only [trOwn]; iframe Hocfg; ipureintro; exact Hsz0
        wp_apply wp_raft_switchToConfig c'.cfg r id s tv cfgv trk prs' pvs' tl c Q
            (fun _ _ => Hmk) Hltz Hcand
            (fun hl => by
              simp only at Hpk; rw [Hli'] at Hpk
              exact Hpk.prOkN (fun v p hv => Hok0.lookup hl hv) (fun hns => Hli2 hns hl))
          Htrg $$ [$Htrkf $Hcore $Hback $Hvotes $Hnew $Htl $Hold $Hfire]
          as %cs %xs %os %ls %lns %s' ⟨Hphys, Hcs, %Hcs0, %Hsw, Hcap⟩
        · ipureintro; exact Hmi
        try wp_auto
        iapply HΦ $$ %cs %xs %os %ls %lns %s'
        iframe Hphys Hcc Hcs Hcap
        ipureintro
        exact ⟨Hcs0, prs', pvs', Hpd, Hmk, Hsw⟩
      · -- `changer.EnterJoint(autoLeave, cc.Changes...)`
        simp only at Happ
        iunfold ownConfChangeV2 at Hcc
        icases Hcc with ⟨%pt, %chs, %ls, %cs, %uf, %Hnn, HT0, #cT, HCh, Hch, #Hccs, HC0, #Hcs, #Hpb⟩
        wp_auto
        wp_apply wp_Changer_EnterJoint _ { Tracker' := tv, LastIndex' := li } c s.progress pvs al
            chs ls ccm.changes (DFrac.own 1) dq (DFrac.own 1) DFrac.discard (DFrac.own 1) Hmi
          $$ [$Hch $Htc $changer]
          as %cfgv %trk %err ⟨-, Hch, Hotc, Hres⟩
        · iexact Hccs
        ihave Hcc : ownConfChangeV2 cc dq ccm $$ [HT0 HCh Hch HC0]
        · iunfold ownConfChangeV2
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
        iunfold ownTrackerCC at Hotc
        icases Hotc with ⟨Hocfg, -, -⟩
        ihave Hold : trOwn (GF := GF) s.gh.tr iprop(ownCfgCC tv.Config' (DFrac.own 1) c ∗ ⌜CfgSizeOk c⌝)
          $$ [Hocfg]
        · cases s.gh.tr
          · iclear Hocfg; simp only [trOwn]; iempintro
          · simp only [trOwn]; iframe Hocfg; ipureintro; exact Hsz0
        wp_apply wp_raft_switchToConfig c'.cfg r id s tv cfgv trk prs' pvs' tl c Q
            (fun _ _ => Hmk) Hltz Hcand
            (fun hl => by
              simp only at Hpk; rw [Hli'] at Hpk
              exact Hpk.prOkN (fun v p hv => Hok0.lookup hl hv) (fun hns => Hli2 hns hl))
          Htrg $$ [$Htrkf $Hcore $Hback $Hvotes $Hnew $Htl $Hold $Hfire]
          as %cs %xs %os %ls %lns %s' ⟨Hphys, Hcs, %Hcs0, %Hsw, Hcap⟩
        · ipureintro; exact Hmi
        try wp_auto
        iapply HΦ $$ %cs %xs %os %ls %lns %s'
        iframe Hphys Hcc Hcs Hcap
        ipureintro
        exact ⟨Hcs0, prs', pvs', Hpd, Hmk, Hsw⟩

end proof

end EtcdGrove
end Perennial
