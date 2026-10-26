/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvwitness/KV__RemoveMember.lean`.
Lean-first (no Rocq counterpart), 2026-10-15 (stage N). raft v3.7 (2026-10-16, stage R6b): the
change is a fresh `&pb.ConfChange{Type: ConfChangeRemoveNode.Enum(), NodeId: new(id)}`, its two
cells frozen (`cellRO_alloc`), owned (`ownCCV1_of_struct`), passed as a `ConfChangeI`.
-/
module

public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.KV__RemoveMember
public import RaftWitness.Spec.go_etcd_io.raft.v3.node__ProposeConfChange
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.ConfChangeType__Enum

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]
variable [KVStor GF]

theorem KV.RemoveMember.wp_proof
    (wp_node_ProposeConfChange : node.ProposeConfChange.spec (GF := GF) (hG := hG))
    (wp_ConfChangeType_Enum : raftpb.ConfChangeType.Enum.spec (GF := GF) (hG := hG)) :
    KV.RemoveMember.spec (GF := GF) (hG := hG) := by
  intro γr γp r id Hok
  wp_start as #Hreg
  iunfold isKV at Hreg
  icases Hreg with ⟨%id0, %n, %st, #Hrep⟩
  iunfold isReplica at Hrep
  iNamed Hrep
  ihave #Hraftinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 $$ []
  · iPkgInit
  ihave #Hpbinit : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto
  wp_apply context.wp_Background
  rw [show raftpb.ConfChangeRemoveNode = #((W32 1 : raftpb.ConfChangeType)) from rfl]
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_ConfChangeType_Enum (W32 1) as %pty Hpty
  imod cellRO_alloc $$ Hpty with #cTy
  imod cellRO_alloc $$ «$v1» with #cN
  wp_alloc cc as Hcc
  -- the fresh `ConfChange`, owned: `rmCC id`
  imod ownCCV1_of_struct cc (⟨zero_val _, pty, «$v1_ptr», slice.nil, null, slice.nil, 0⟩ : raftpb.ConfChange)
      (rmCC id) ⊤ rfl $$ [Hcc] with Hcc
  · iframe Hcc
    simp only [rmCC]
    iframe cTy cN
    isplitl []
    · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
    iapply ownSlice_nil
  ihave Hcci : ownCCI (interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #cc)
      (DFrac.own 1) (some (.v1 (rmCC id))) $$ [Hcc]
  · simp only [ownCCI]
    iexists cc
    iframe Hcc
    ipureintro; rfl
  wp_auto
  ihave #Hbg := nodeCtx_background (GF := GF) bgCd
  wp_apply wp_node_ProposeConfChange γp.node id0 n _ (.v1 (rmCC id)) (DFrac.own 1)
      context.backgroundCtxVal bgCd (by rw [Hraft]; exact Hok)
      $$ [$Hraftinit $HisNode $Hbg $Hcci] as %err -
  iapply HΦ
  itrivial

end proof

end kvwitness
end EtcdGrove
end Perennial
