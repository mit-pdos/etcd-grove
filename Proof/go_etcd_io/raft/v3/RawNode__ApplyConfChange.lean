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

theorem RawNode.ApplyConfChange.wp_proof
    (wp_ConfChange_AsV2 : raftpb.ConfChange.AsV2.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_AsV2 : raftpb.ConfChangeV2.AsV2.spec (GF := GF) (hG := hG))
    (wp_raft_applyConfChange : raft.applyConfChange.spec (GF := GF) (hG := hG)) :
    RawNode.ApplyConfChange.spec (GF := GF) (hG := hG) := by
  intro γ rn id rs c o dq Hap0
  wp_start as H
  iNamed H
  iNamed Hrn
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
      imod rawNode_applyCC_reseal γ rn id rs s s' ps rnv sv steps Hrel Hin Hasync Hdlen Hunp Hsnap
        Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hok
        $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs with Hrn
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
      imod rawNode_applyCC_reseal γ rn id rs s s' ps rnv sv steps Hrel Hin Hasync Hdlen Hunp Hsnap
        Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hok
        $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs with Hrn
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
