/- Lean-first (no Rocq counterpart), 2026-10-13: reconfiguration stage D. -/
module

public import Spec.go_etcd_io.raft.v3.RawNode__ApplyConfChange
public import Spec.go_etcd_io.raft.v3.raft__applyConfChange
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__AsV2
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__AsV2
-- `rawNode_applyCC_reseal`
public import Proof.go_etcd_io.raft.v3.InvNodeRun
public import Proof.go_etcd_io.raft.v3.InvRawnodeC

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3
open RawNodeOwnAccess

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The dynamic model's reading of `ApplyCCOkC c'` (2026-10-14, stage B7 part 2): at a ghost part
over `c'`, a non-leader takes no step, a leader that stays a voter takes `reMatch`, `commit` by a
joint quorum of `c'` and `sendApps` (an `MsgApp` carrying its commit index, `ReplSends`), and a
removed or demoted leader takes `reMatch` and steps down (`StepR.stepDown`, with
`StepDownOnRemoval`). `applyCCOkC_step`'s `StepR` version: `StepR` has the step-down. -/
theorem applyCCOkC_stepR {Adm : List raftpb.Entry → CCState → Prop} {dec : CCDec} (c' : CfgM)
    (id : w64) (s s' : NState) (g : RGh) (H : ApplyCCOkC c' id s s') (hc : g.cfg.cfg = c') :
    StepR Adm dec id (rOf s g) [] (rOf s' g) := by
  obtain ⟨prs, pvs, -, Hmk, Hsw⟩ := H
  unfold SwitchOkC at Hsw
  by_cases Hl : s.role = .leader
  · rw [if_pos (show ({ s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } :
        NState).role = .leader from Hl)] at Hsw
    have Hpl : (toPState s).role = .leader := by simp [toPState, Hl, proleRole]
    -- the new `Progress` values
    have H1 : StepCF c' id (toPState s) []
        (toPState { s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id }) := by
      have e : toPState { s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } =
          { toPState s with matched := prvalsMatch pvs } := by simp [toPState, Hl]
      rw [e]
      refine .reMatch _ _ Hpl (fun v i hv => ?_)
      simp only [prvalsMatch, GMap.lookup_fmap'] at hv
      cases hp : pvs !! v with
      | none => rw [hp] at hv; cases hv
      | some p' =>
        rw [hp] at hv
        simp only [Option.map_some, Option.some.injEq] at hv
        subst hv
        rcases Hmk v p' hp with h0 | ⟨p, hp0, hm⟩
        · exact .inl h0
        · right
          simp [toPState, Hl, prvalsMatch, GMap.lookup_fmap', hp0, hm]
    have Hz := rOf_pci_zero s g
    by_cases Hv : id ∈ c'.voters
    · rw [if_pos Hv] at Hsw
      obtain ⟨c, ms, pvs2, lt', Hc, Hms, Hmm, rfl⟩ := Hsw
      generalize Hs1 : ({ s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } :
        NState) = s1 at H1 Hc Hms Hmm
      have Hl1 : s1.role = .leader := by rw [← Hs1]; exact Hl
      have Hpl1 : (toPState s1).role = .leader := by simp [toPState, Hl1, proleRole]
      -- the commit
      have H2 : StepCF c' id (toPState s1) []
          (toPState { s1 with logst := { s1.logst with committed := c } }) := by
        rcases Hc with rfl | ⟨Hlt, Hle, Htm, Hq⟩
        · have e : ({ s1 with logst := { s1.logst with committed := s1.logst.committed } } : NState)
              = s1 := by cases s1; rfl
          rw [e]; exact .refl _
        · have e : toPState { s1 with logst := { s1.logst with committed := c } } =
              { toPState s1 with commit := c } := by simp [toPState, Hl1]
          rw [e]
          exact .commit _ c Hpl1 Hlt Hle Htm Hq
      generalize Hs2 : ({ s1 with logst := { s1.logst with committed := c } } : NState) = s2
        at H2 Hms
      have Hl2 : s2.role = .leader := by rw [← Hs2]; exact Hl1
      -- the appends
      have H3 : StepCF c' id (toPState s2) []
          (toPState { sendMsgs s2 ms with prvals := pvs2, lt := lt' }) := by
        have e : toPState { sendMsgs s2 ms with prvals := pvs2, lt := lt' } =
            toPState { sendMsgs s2 ms with prvals := pvs2 } := rfl
        rw [e, toPState_prvals (sendMsgs s2 ms) pvs2 (fun _ => by
          rw [Hmm]; rw [← Hs2]; rfl), toPState_sendMsgs]
        exact .sendApps _ ms (by simp [toPState, Hl2, proleRole]) Hms.replOk
          (fun m hm => (Hms m hm).2)
      have HF := StepCF.trans _ _ _ _ _ H1 (StepCF.trans _ _ _ _ _ H2 H3)
      have HR := HF.toR (Adm := Adm) (dec := dec) (rOf s g) rfl hc Hz
      have Hfr : RFrame s { sendMsgs s2 ms with prvals := pvs2, lt := lt' } := by
        refine ⟨?_, ?_, fun _ => ⟨Hl, ?_⟩⟩ <;> (rw [← Hs2, ← Hs1]; try rfl)
      rw [rOf_frame _ _ g Hfr]
      exact HR
    · -- removed or demoted: `reMatch`, then the step-down
      rw [if_neg Hv] at Hsw
      obtain ⟨pvs', rfl⟩ := Hsw
      generalize Hs1 : ({ s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } :
        NState) = s1 at H1 ⊢
      have HR1 := H1.toR (Adm := Adm) (dec := dec) (rOf s g) rfl hc Hz
      have Hfr1 : RFrame s s1 := by
        refine ⟨?_, ?_, fun _ => ⟨Hl, ?_⟩⟩ <;> (rw [← Hs1]; try rfl)
      rw [← rOf_frame _ _ g Hfr1] at HR1
      have Hl1 : s1.role = .leader := by rw [← Hs1]; exact Hl
      have Hrl : (rOf s1 g).p.role = .leader := by simp [rOf, toPState, Hl1, proleRole]
      have HR2 := StepR.stepDown (Adm := Adm) (dec := dec) (id := id) (rOf s1 g) Hrl
        (by simp only [rOf]; rw [hc]; exact Hv)
      have Ht1 : s1.term = s.term := by rw [← Hs1]
      have e : RState.mk (pbecomeFollower (rOf s1 g).p (rOf s1 g).p.term (W64 0))
          (rOf s1 g).applied (W64 0) (rOf s1 g).snap (rOf s1 g).cidx (rOf s1 g).cfg (rOf s1 g).fp =
          rOf ({ becomeFollower s1 s1.term (W64 0) with prvals := pvs' } : NState) g := by
        have h1 := toPState_prvals (becomeFollower s1 s1.term (W64 0)) pvs'
          (fun h => by simp [becomeFollower] at h)
        have h2 := toPState_becomeFollower s1 s1.term (W64 0)
        unfold rOf
        rw [h1, h2]
        simp [pciR, becomeFollower, toPState, resetTo0, resetTo]
      rw [e] at HR2
      exact .trans _ _ _ _ _ HR1 HR2
  · rw [if_neg (show ¬ ({ s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } :
        NState).role = .leader from Hl)] at Hsw
    subst Hsw
    have e : rOf { s with progress := prs, prvals := pvs, isLearner := learnerOfC c' id } g =
        rOf s g := by
      unfold rOf pciR
      simp [toPState, Hl]
    rw [e]
    exact .refl _

theorem RawNode.ApplyConfChange.wp_proof
    (wp_ConfChange_AsV2 : raftpb.ConfChange.AsV2.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_AsV2 : raftpb.ConfChangeV2.AsV2.spec (GF := GF) (hG := hG))
    (wp_raft_applyConfChange : raft.applyConfChange.spec (GF := GF) (hG := hG)) :
    RawNode.ApplyConfChange.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs c o dq Hm Hap0
  wp_start as H
  iNamed H
  iNamed Hrn
  icases ownRawNode_static_open γ rs Hm fp cf rnv.raft' id s $$ Hphys Hghost with ⟨Hphys, Hghost⟩
  have Hrel : NStateRel s (toPState s) := ⟨rfl, Hwf⟩
  have Hin := Hin Hm
  rcases o with m | m
  · -- a `ConfChange`: `AsV2` makes the one change
    simp only [ownCCI, ownCCV1]
    icases Hc with ⟨%v, %Hcv, %Hvm, Hctx⟩
    subst Hcv
    wp_auto
    wp_apply wp_ConfChange_AsV2 as %v2 ⟨%Hv2, Hch⟩
    obtain ⟨Hty, Hnid, Hid⟩ := Hvm
    have Hap : CCApplies γ.reCfg id v2.Transition' [({ Type' := v.Type', NodeId' := v.NodeId' } :
        raftpb.ConfChangeSingle)] := by
      rw [Hv2.1, Hty, Hnid]; exact Hap0
    by_cases Hsh : CCShrink γ.reCfg (ccV2Of (.v1 m)).1 (ccV2Of (.v1 m)).2
    · -- a shrinking change: as in stage L
      have Hn0 : CCShrink γ.reCfg v2.Transition' [({ Type' := v.Type', NodeId' := v.NodeId' } :
          raftpb.ConfChangeSingle)] := by
        rw [Hv2.1, Hty, Hnid]; exact Hsh
      icases ownRaftPhys_progress_dom γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsub, Hphys⟩
      icases ownRaftPhys_progress_size γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsz, Hphys⟩
      obtain ⟨lrn', Hd', Hsz', Hn⟩ := applyCC_of_shrink γ.reCfg s.progress _ _ Hn0 Hsub Hsz
      wp_apply +noauto (raft.applyConfChange.spec_simple wp_raft_applyConfChange) γ.reCfg rnv.raft' id s v2 _ (DFrac.own 1) lrn' Hd'
        Hsz' Hn
        $$ [$Hphys $Hch] as %cs %xs %ls %s' ⟨Hphys, -, Hvoters, Hls, %Hcs0, %Hok⟩
      imod rawNode_applyCC_reseal γ rn id rs s s' _ rnv sv steps Hm Hrel Hin Hasync Hdlen Hunp
        Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hok
        $$ Hrn Hphys Hghost Hsdrf Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs with Hrn
      try wp_auto
      iapply HΦ
      simp only [named]
      iframe Hvoters Hls
      isplitl [Hctx]
      · try simp only [ownCCI, ownCCV1]
        iexists v
        isplitr
        · ipureintro; rfl
        iframe Hctx
        ipureintro; exact ⟨Hty, Hnid, Hid⟩
      iframe
      ileft
      iframe Hrn
      ipureintro
      exact ⟨Hsh, Hcs0.1, fun k hk => Hd' k ((GMap.elem_of_elements _ _).1 (Hcs0.2.1.mem_iff.1 hk)),
        Hcs0.2.2⟩
    · -- any other change: detached, at the new configuration
      icases ownRaftPhys_progress_dom γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsub, Hphys⟩
      icases ownRaftPhys_progress_size γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsz, Hphys⟩
      have HdL : ∀ k, k ∈ domSet s.progress \ γ.reCfg → k ∉ γ.reCfg :=
        fun k hk => ((GMap.elem_of_difference _ _ _).1 hk).2
      have HU : γ.reCfg ∪ (domSet s.progress \ γ.reCfg) = domSet s.progress := by
        apply GMap.set_eq; intro k
        rw [GMap.elem_of_union, GMap.elem_of_difference]
        constructor
        · rintro (h | ⟨h, -⟩)
          · exact (GMap.elem_of_subseteq _ _).1 Hsub k h
          · exact h
        · intro h
          by_cases hk : k ∈ γ.reCfg
          · exact .inl hk
          · exact .inr ⟨h, hk⟩
      have HszL : (GMap.size (γ.reCfg ∪ (domSet s.progress \ γ.reCfg)) : Int) ≤ 2 ^ 62 := by
        rw [HU, GMap.size_dom]; exact Hsz
      obtain ⟨c', Happ, Hsz', Hin'⟩ := Hap _ HdL HszL
      have Happ' := Happ
      rw [Hv2.1, Hty, Hnid] at Happ'
      ihave Hphys := ownRaftPhys_toC' $$ Hphys
      wp_apply +noauto wp_raft_applyConfChange (CfgM.simple γ.reCfg (domSet s.progress \ γ.reCfg))
          rnv.raft' id s v2 _ (DFrac.own 1) c' (by rw [cfgStateC_simple]; exact Happ) Hsz'
          (fun _ h => absurd Hin' h) (fun _ => Hin')
        $$ [$Hphys $Hch] as %cs %xs %os %ls %lns %s' ⟨Hphys, Hch, Hvoters, Hos, Hls, Hlns, %Hcs0, %Hok⟩
      try wp_auto
      iapply HΦ
      simp only [named]
      iframe Hvoters Hls
      isplitl [Hctx]
      · try simp only [ownCCI, ownCCV1]
        iexists v
        isplitr
        · ipureintro; rfl
        iframe Hctx
        ipureintro; exact ⟨Hty, Hnid, Hid⟩
      iframe
      iright
      isplitr
      · ipureintro; exact Hsh
      iexists (domSet s.progress \ γ.reCfg), c', s, s', os, lns
      iframe Hos Hlns
      isplitl [Hrn Hphys Hsteps Hsteps_cap Hpown]
      · iapply ownRawNodeC_intro c'.cfg rn id s' rnv sv steps rs.steps Hasync
          $$ Hrn Hphys Hsoft Hsteps Hsteps_cap Hpown
      ipureintro
      exact ⟨HdL, Happ', Hcs0.1, Hcs0.2.1, Hcs0.2.2.1, Hcs0.2.2.2.1, Hcs0.2.2.2.2, Hok⟩
  · -- a `ConfChangeV2`: `AsV2` is itself
    simp only [ownCCI, ownCCV2]
    icases Hc with ⟨%v, %Hcv, %Htr, Hch, Hctx⟩
    subst Hcv
    wp_auto
    wp_apply wp_ConfChangeV2_AsV2
    have Hap : CCApplies γ.reCfg id v.Transition' m.changes := by rw [Htr]; exact Hap0
    by_cases Hsh : CCShrink γ.reCfg (ccV2Of (.v2 m)).1 (ccV2Of (.v2 m)).2
    · have Hn0 : CCShrink γ.reCfg v.Transition' m.changes := by rw [Htr]; exact Hsh
      icases ownRaftPhys_progress_dom γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsub, Hphys⟩
      icases ownRaftPhys_progress_size γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsz, Hphys⟩
      obtain ⟨lrn', Hd', Hsz', Hn⟩ := applyCC_of_shrink γ.reCfg s.progress _ _ Hn0 Hsub Hsz
      wp_apply +noauto (raft.applyConfChange.spec_simple wp_raft_applyConfChange) γ.reCfg rnv.raft' id s v _ dq lrn' Hd' Hsz' Hn
        $$ [$Hphys $Hch] as %cs %xs %ls %s' ⟨Hphys, Hch, Hvoters, Hls, %Hcs0, %Hok⟩
      imod rawNode_applyCC_reseal γ rn id rs s s' _ rnv sv steps Hm Hrel Hin Hasync Hdlen Hunp
        Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hok
        $$ Hrn Hphys Hghost Hsdrf Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs with Hrn
      try wp_auto
      iapply HΦ
      simp only [named]
      iframe Hvoters Hls
      isplitl [Hch Hctx]
      · try simp only [ownCCI, ownCCV2]
        iexists v
        isplitr
        · ipureintro; rfl
        iframe Hch Hctx
        ipureintro; exact Htr
      iframe
      ileft
      iframe Hrn
      ipureintro
      exact ⟨Hsh, Hcs0.1, fun k hk => Hd' k ((GMap.elem_of_elements _ _).1 (Hcs0.2.1.mem_iff.1 hk)),
        Hcs0.2.2⟩
    · -- any other change: detached, at the new configuration
      icases ownRaftPhys_progress_dom γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsub, Hphys⟩
      icases ownRaftPhys_progress_size γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsz, Hphys⟩
      have HdL : ∀ k, k ∈ domSet s.progress \ γ.reCfg → k ∉ γ.reCfg :=
        fun k hk => ((GMap.elem_of_difference _ _ _).1 hk).2
      have HU : γ.reCfg ∪ (domSet s.progress \ γ.reCfg) = domSet s.progress := by
        apply GMap.set_eq; intro k
        rw [GMap.elem_of_union, GMap.elem_of_difference]
        constructor
        · rintro (h | ⟨h, -⟩)
          · exact (GMap.elem_of_subseteq _ _).1 Hsub k h
          · exact h
        · intro h
          by_cases hk : k ∈ γ.reCfg
          · exact .inl hk
          · exact .inr ⟨h, hk⟩
      have HszL : (GMap.size (γ.reCfg ∪ (domSet s.progress \ γ.reCfg)) : Int) ≤ 2 ^ 62 := by
        rw [HU, GMap.size_dom]; exact Hsz
      obtain ⟨c', Happ, Hsz', Hin'⟩ := Hap _ HdL HszL
      have Happ' := Happ
      rw [Htr] at Happ'
      ihave Hphys := ownRaftPhys_toC' $$ Hphys
      wp_apply +noauto wp_raft_applyConfChange (CfgM.simple γ.reCfg (domSet s.progress \ γ.reCfg))
          rnv.raft' id s v _ dq c' (by rw [cfgStateC_simple]; exact Happ) Hsz'
          (fun _ h => absurd Hin' h) (fun _ => Hin')
        $$ [$Hphys $Hch] as %cs %xs %os %ls %lns %s' ⟨Hphys, Hch, Hvoters, Hos, Hls, Hlns, %Hcs0, %Hok⟩
      try wp_auto
      iapply HΦ
      simp only [named]
      iframe Hvoters Hls
      isplitl [Hch Hctx]
      · try simp only [ownCCI, ownCCV2]
        iexists v
        isplitr
        · ipureintro; rfl
        iframe Hch Hctx
        ipureintro; exact Htr
      iframe
      iright
      isplitr
      · ipureintro; exact Hsh
      iexists (domSet s.progress \ γ.reCfg), c', s, s', os, lns
      iframe Hos Hlns
      isplitl [Hrn Hphys Hsteps Hsteps_cap Hpown]
      · iapply ownRawNodeC_intro c'.cfg rn id s' rnv sv steps rs.steps Hasync
          $$ Hrn Hphys Hsoft Hsteps Hsteps_cap Hpown
      ipureintro
      exact ⟨HdL, Happ', Hcs0.1, Hcs0.2.1, Hcs0.2.2.1, Hcs0.2.2.2.1, Hcs0.2.2.2.2, Hok⟩

end proof

end EtcdGrove
end Perennial
