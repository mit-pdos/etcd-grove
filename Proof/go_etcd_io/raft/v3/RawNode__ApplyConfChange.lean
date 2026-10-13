/- Lean-first (no Rocq counterpart), 2026-10-13: reconfiguration stage D. -/
module

public import Spec.go_etcd_io.raft.v3.RawNode__ApplyConfChange
public import Spec.go_etcd_io.raft.v3.raft__applyConfChange
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__AsV2
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__AsV2
-- `rawNode_applyCC_reseal`
public import Proof.go_etcd_io.raft.v3.InvNodeRun

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
  intro γ rn id rs c o dq Hnoop
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
    have Hn : ccApplyM v2.Transition' [({ Type' := v.Type', NodeId' := v.NodeId' } :
        raftpb.ConfChangeSingle)] (cfgState γ.reCfg) = some (cfgState γ.reCfg) := by
      rw [Hv2.1, Hty, Hnid]; exact Hnoop
    wp_apply +noauto wp_raft_applyConfChange γ.reCfg rnv.raft' id s v2 _ (DFrac.own 1) Hin Hn
      $$ [$Hphys $Hch] as %cs %xs %s' ⟨Hphys, -, Hvoters, %Hxs, %Hcs0, %Hok⟩
    imod rawNode_applyCC_reseal γ rn id rs s s' ps rnv sv steps Hrel Hin Hasync Hdlen Hunp Hsnap
      Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hok
      $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs with Hrn
    try wp_auto
    iapply HΦ
    simp only [named]
    iframe Hrn Hvoters
    isplitl [Hctx]
    · try simp only [ownCCI, ownCCV1]
      iexists v
      isplitr
      · ipureintro; rfl
      iframe Hctx
      ipureintro; exact ⟨Hty, Hnid, Hid⟩
    iframe
    ipureintro; exact ⟨Hxs, Hcs0⟩
  · -- a `ConfChangeV2`: `AsV2` is itself
    simp only [ownCCI, ownCCV2]
    icases Hc with ⟨%v, %Hcv, %Htr, Hch, Hctx⟩
    subst Hcv
    wp_auto
    wp_apply wp_ConfChangeV2_AsV2
    have Hn : ccApplyM v.Transition' m.changes (cfgState γ.reCfg) = some (cfgState γ.reCfg) := by
      rw [Htr]; exact Hnoop
    wp_apply +noauto wp_raft_applyConfChange γ.reCfg rnv.raft' id s v _ dq Hin Hn
      $$ [$Hphys $Hch] as %cs %xs %s' ⟨Hphys, Hch, Hvoters, %Hxs, %Hcs0, %Hok⟩
    imod rawNode_applyCC_reseal γ rn id rs s s' ps rnv sv steps Hrel Hin Hasync Hdlen Hunp Hsnap
      Hstok Htrm Hstor Hpvoff Hrs_out Hrs_unst Hrs_clb Hok
      $$ Hrn Hphys Hghost Hsoft Hsteps Hsteps_cap Hpend Hpown Hdeliv Hstrecs with Hrn
    try wp_auto
    iapply HΦ
    simp only [named]
    iframe Hrn Hvoters
    isplitl [Hch Hctx]
    · try simp only [ownCCI, ownCCV2]
      iexists v
      isplitr
      · ipureintro; rfl
      iframe Hch Hctx
      ipureintro; exact Htr
    iframe
    ipureintro; exact ⟨Hxs, Hcs0⟩

end proof

end EtcdGrove
end Perennial
