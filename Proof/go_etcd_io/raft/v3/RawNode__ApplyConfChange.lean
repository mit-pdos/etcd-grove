/- Lean-first (no Rocq counterpart), 2026-10-13: reconfiguration stage D.

raft v3.7 (2026-10-16, stage R5): the conf change is a pointer (`ownCCI`): a `*ConfChange`'s
`AsV2` returns a fresh `*ConfChangeV2` (`ownCCV2 v 1 m.asV2`, whose transition and changes are
`ccV2Of (.v1 m)` by definition), a `*ConfChangeV2`'s is itself; `applyConfChange` returns a fresh
`*pb.ConfState` (`csPts cs 1 … true`), handed to the caller. -/
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

theorem RawNode.ApplyConfChange.wp_proof
    (wp_ConfChange_AsV2 : raftpb.ConfChange.AsV2.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_AsV2 : raftpb.ConfChangeV2.AsV2.spec (GF := GF) (hG := hG))
    (wp_raft_applyConfChange : raft.applyConfChange.spec (GF := GF) (hG := hG)) :
    RawNode.ApplyConfChange.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs c o dq k0 e0 cs0 Hap0 Hdyn
  wp_start as H
  iNamed H
  iNamed Hrn
  have Hmode : (∃ dec c0 h0 h1, rs.mode = .dyn dec c0 h0 h1) ∨ rs.mode = .static := by
    cases rs.mode with
    | static => exact .inr rfl
    | dyn dec c0 h0 h1 => exact .inl ⟨dec, c0, h0, h1, rfl⟩
  rcases Hmode with ⟨dec, c0, h0, h1, hm⟩ | hm
  · have Hpre := Hdyn dec c0 h0 h1 hm
    rcases o with m | m
    · simp only [ownCCI]
      icases Hc with ⟨%p, %Hcv, Hc1⟩
      subst Hcv
      wp_auto_lc 1
      wp_apply wp_ConfChange_AsV2 p dq m $$ [$Hc1] as %v2 ⟨Hc1, Hch⟩
      wp_apply wp_applyConf_dyn wp_raft_applyConfChange γ rn id rs dec c0 h0 h1 hm k0 e0
          cs0 v2 m.asV2 (DFrac.own 1) Hpre s cf fp rnv sv hprev steps Hwf Hin
          Hasync Hdlen Hunp Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl
        $$ [$Hrn $Hphys $Hghost $Hsdrf $Hsoft $Hhard $Hsteps $Hsteps_cap $Hpend $Hdeliv $Hstrecs
          $Hch $Hlc1] as %cs %xs %os %ls %lns ⟨Hrn, -, Hcs, %Hcs0⟩
      try wp_auto
      iapply HΦ $$ %cs %(ConfStateM.mk xs ls os lns cs0.cfg.autoLeave)
      simp only [named]
      iframe Hcs
      isplitl [Hc1]
      · try simp only [ownCCI]
        iexists p
        iframe Hc1
        ipureintro; rfl
      iright
      isplitr
      · ipureintro; rw [hm]; rfl
      iframe Hrn
      ipureintro; exact ⟨Hcs0.1, Hcs0.2.1, Hcs0.2.2.1, Hcs0.2.2.2, trivial⟩
    · simp only [ownCCI]
      icases Hc with ⟨%p, %Hcv, Hch⟩
      subst Hcv
      wp_auto_lc 1
      wp_apply wp_ConfChangeV2_AsV2
      wp_apply wp_applyConf_dyn wp_raft_applyConfChange γ rn id rs dec c0 h0 h1 hm k0 e0
          cs0 p m dq Hpre s cf fp rnv sv hprev steps Hwf Hin
          Hasync Hdlen Hunp Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl
        $$ [$Hrn $Hphys $Hghost $Hsdrf $Hsoft $Hhard $Hsteps $Hsteps_cap $Hpend $Hdeliv $Hstrecs
          $Hch $Hlc1] as %cs %xs %os %ls %lns ⟨Hrn, Hch, Hcs, %Hcs0⟩
      try wp_auto
      iapply HΦ $$ %cs %(ConfStateM.mk xs ls os lns cs0.cfg.autoLeave)
      simp only [named]
      iframe Hcs
      isplitl [Hch]
      · try simp only [ownCCI]
        iexists p
        iframe Hch
        ipureintro; rfl
      iright
      isplitr
      · ipureintro; rw [hm]; rfl
      iframe Hrn
      ipureintro; exact ⟨Hcs0.1, Hcs0.2.1, Hcs0.2.2.1, Hcs0.2.2.2, trivial⟩
  have Hm := hm
  have Hap0 := Hap0 hm
  icases ownRawNode_static_open γ rs Hm fp cf rnv.raft' id s $$ Hphys Hghost with
    ⟨Hphys, Hghost, %Htrk, %Hnl, #Hcl⟩
  have Hrel : NStateRel s (toPState s) := ⟨rfl, Hwf⟩
  have Hin := Hin Hm
  rcases o with m | m
  · -- a `ConfChange`: `AsV2` makes the one change, a fresh `*ConfChangeV2`
    simp only [ownCCI]
    icases Hc with ⟨%p, %Hcv, Hc1⟩
    subst Hcv
    wp_auto_lc 1
    wp_apply wp_ConfChange_AsV2 p dq m $$ [$Hc1] as %v2 ⟨Hc1, Hch⟩
    have Hap : CCApplies γ.reCfg id m.asV2.transition m.asV2.changes := Hap0
    by_cases Hsh : CCShrink γ.reCfg (ccV2Of (.v1 m)).1 (ccV2Of (.v1 m)).2
    · -- a shrinking change: as in stage L
      have Hn0 : CCShrink γ.reCfg m.asV2.transition m.asV2.changes := Hsh
      icases ownRaftPhys_progress_dom γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsub, Hphys⟩
      icases ownRaftPhys_progress_size γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsz, Hphys⟩
      obtain ⟨lrn', Hd', Hsz', Hn, Hlp⟩ := applyCC_of_shrink γ.reCfg s.progress _ _ Hn0 Hsub Hsz
      icases ownRaftGhost_ns_last γ id s Hnl $$ Hghost with ⟨%Hli2, Hghost⟩
      wp_apply +noauto (raft.applyConfChange.spec_simple wp_raft_applyConfChange) γ.reCfg rnv.raft'
          id s v2 m.asV2 (DFrac.own 1) lrn' Hd' Hsz' Hn Hli2
        $$ [$Hphys $Hch] as %cs %xs %ls %s' ⟨Hphys, -, Hcs, %Hcs0, %Hok, %Hdom'⟩
      imod rawNode_applyCC_reseal γ rn id rs s s' _ rnv sv hprev steps Hm Hrel Hin Hasync Hdlen Hunp
        Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl Hok
        (trackedOk_shrink Htrk Hlp Hdom') Hnl
        $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hcl Hlc1 with Hrn
      try wp_auto
      iapply HΦ $$ %cs %(ConfStateM.mk xs ls [] [] false)
      simp only [named]
      iframe Hcs
      isplitl [Hc1]
      · try simp only [ownCCI]
        iexists p
        iframe Hc1
        ipureintro; rfl
      ileft
      isplitr
      · ipureintro; exact Hm
      ileft
      iframe Hrn
      ipureintro
      exact ⟨Hsh, Hcs0.1, fun k hk => Hd' k ((GMap.elem_of_elements _ _).1 (Hcs0.2.mem_iff.1 hk)),
        trivial, trivial, trivial⟩
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
      have Happ' : ccApplyM (ccV2Of (.v1 m)).1 (ccV2Of (.v1 m)).2 (cfgState γ.reCfg (domSet s.progress \ γ.reCfg)) = some c' := Happ
      ihave Hphys := ownRaftPhys_toC' $$ Hphys
      icases ownRaftGhost_ns_last γ id s Hnl $$ Hghost with ⟨%Hli2, Hghost⟩
      wp_apply +noauto wp_raft_applyConfChange (CfgM.simple γ.reCfg (domSet s.progress \ γ.reCfg))
          rnv.raft' id s v2 m.asV2 (DFrac.own 1) c' (by rw [cfgStateC_simple]; exact Happ) Hsz'
          (fun _ h => absurd Hin' h) (fun _ => Hin') Hli2
        $$ [$Hphys $Hch] as %cs %xs %os %ls %lns %s' ⟨Hphys, -, Hcs, %Hcs0, %Hok⟩
      try wp_auto
      iapply HΦ $$ %cs %(ConfStateM.mk xs ls os lns c'.cfg.autoLeave)
      simp only [named]
      iframe Hcs
      isplitl [Hc1]
      · try simp only [ownCCI]
        iexists p
        iframe Hc1
        ipureintro; rfl
      ileft
      isplitr
      · ipureintro; exact Hm
      iright
      isplitr
      · ipureintro; exact Hsh
      iexists (domSet s.progress \ γ.reCfg), c', s, s'
      ihave Hpown := pendList_forget γ id steps rs.steps $$ Hpend
      isplitl [Hrn Hphys Hsteps Hsteps_cap Hpown]
      · iapply ownRawNodeC_intro c'.cfg rn id s' rnv sv hprev steps rs.steps Hasync
          $$ Hrn Hphys Hsoft [Hhard] Hsteps Hsteps_cap Hpown
        · iapply prevHS_hsRO $$ Hhard
      ipureintro
      exact ⟨HdL, Happ', Hcs0.1, Hcs0.2.1, Hcs0.2.2.1, Hcs0.2.2.2, rfl, Hok⟩
  · -- a `ConfChangeV2`: `AsV2` is itself
    simp only [ownCCI]
    icases Hc with ⟨%p, %Hcv, Hch⟩
    subst Hcv
    wp_auto_lc 1
    wp_apply wp_ConfChangeV2_AsV2
    have Hap : CCApplies γ.reCfg id m.transition m.changes := Hap0
    by_cases Hsh : CCShrink γ.reCfg (ccV2Of (.v2 m)).1 (ccV2Of (.v2 m)).2
    · -- a shrinking change: as in stage L
      have Hn0 : CCShrink γ.reCfg m.transition m.changes := Hsh
      icases ownRaftPhys_progress_dom γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsub, Hphys⟩
      icases ownRaftPhys_progress_size γ.reCfg rnv.raft' id s $$ Hphys with ⟨%Hsz, Hphys⟩
      obtain ⟨lrn', Hd', Hsz', Hn, Hlp⟩ := applyCC_of_shrink γ.reCfg s.progress _ _ Hn0 Hsub Hsz
      icases ownRaftGhost_ns_last γ id s Hnl $$ Hghost with ⟨%Hli2, Hghost⟩
      wp_apply +noauto (raft.applyConfChange.spec_simple wp_raft_applyConfChange) γ.reCfg rnv.raft'
          id s p m dq lrn' Hd' Hsz' Hn Hli2
        $$ [$Hphys $Hch] as %cs %xs %ls %s' ⟨Hphys, Hch, Hcs, %Hcs0, %Hok, %Hdom'⟩
      imod rawNode_applyCC_reseal γ rn id rs s s' _ rnv sv hprev steps Hm Hrel Hin Hasync Hdlen Hunp
        Hsnap Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hrnfl Hok
        (trackedOk_shrink Htrk Hlp Hdom') Hnl
        $$ Hrn Hphys Hghost Hsdrf Hsoft Hhard Hsteps Hsteps_cap Hpend Hdeliv Hstrecs Hcl Hlc1 with Hrn
      try wp_auto
      iapply HΦ $$ %cs %(ConfStateM.mk xs ls [] [] false)
      simp only [named]
      iframe Hcs
      isplitl [Hch]
      · try simp only [ownCCI]
        iexists p
        iframe Hch
        ipureintro; rfl
      ileft
      isplitr
      · ipureintro; exact Hm
      ileft
      iframe Hrn
      ipureintro
      exact ⟨Hsh, Hcs0.1, fun k hk => Hd' k ((GMap.elem_of_elements _ _).1 (Hcs0.2.mem_iff.1 hk)),
        trivial, trivial, trivial⟩
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
      have Happ' : ccApplyM (ccV2Of (.v2 m)).1 (ccV2Of (.v2 m)).2 (cfgState γ.reCfg (domSet s.progress \ γ.reCfg)) = some c' := Happ
      ihave Hphys := ownRaftPhys_toC' $$ Hphys
      icases ownRaftGhost_ns_last γ id s Hnl $$ Hghost with ⟨%Hli2, Hghost⟩
      wp_apply +noauto wp_raft_applyConfChange (CfgM.simple γ.reCfg (domSet s.progress \ γ.reCfg))
          rnv.raft' id s p m dq c' (by rw [cfgStateC_simple]; exact Happ) Hsz'
          (fun _ h => absurd Hin' h) (fun _ => Hin') Hli2
        $$ [$Hphys $Hch] as %cs %xs %os %ls %lns %s' ⟨Hphys, Hch, Hcs, %Hcs0, %Hok⟩
      try wp_auto
      iapply HΦ $$ %cs %(ConfStateM.mk xs ls os lns c'.cfg.autoLeave)
      simp only [named]
      iframe Hcs
      isplitl [Hch]
      · try simp only [ownCCI]
        iexists p
        iframe Hch
        ipureintro; rfl
      ileft
      isplitr
      · ipureintro; exact Hm
      iright
      isplitr
      · ipureintro; exact Hsh
      iexists (domSet s.progress \ γ.reCfg), c', s, s'
      ihave Hpown := pendList_forget γ id steps rs.steps $$ Hpend
      isplitl [Hrn Hphys Hsteps Hsteps_cap Hpown]
      · iapply ownRawNodeC_intro c'.cfg rn id s' rnv sv hprev steps rs.steps Hasync
          $$ Hrn Hphys Hsoft [Hhard] Hsteps Hsteps_cap Hpown
        · iapply prevHS_hsRO $$ Hhard
      ipureintro
      exact ⟨HdL, Happ', Hcs0.1, Hcs0.2.1, Hcs0.2.2.1, Hcs0.2.2.2, rfl, Hok⟩

end proof

end EtcdGrove
end Perennial
