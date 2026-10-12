/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/raftNode__start.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__start
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftLoop
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__tick
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__processMessages
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.updateCommittedIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.raftNode__onStop
public import EtcdDeps.Spec.go_etcd_io.raft.v3.IsEmptySnap
public import EtcdDeps.Spec.go_etcd_io.raft.v3.IsEmptyHardState
public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.HardState__GetCommit
public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType
public import Spec.google_golang_org.protobuf.proto.Clone
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Fatal

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem raftNode.start.wp_proof
    (wp_tick : raftNode.tick.spec (GF := GF) (hG := hG))
    (wp_processMessages : raftNode.processMessages.spec (GF := GF) (hG := hG))
    (wp_updateCommittedIndex : updateCommittedIndex.spec (GF := GF) (hG := hG))
    (wp_onStop : raftNode.onStop.spec (GF := GF) (hG := hG))
    (wp_IsEmptySnap : IsEmptySnap.spec (GF := GF) (hG := hG))
    (wp_IsEmptyHardState : IsEmptyHardState.spec (GF := GF) (hG := hG))
    (wp_GetCommit : raftpb.HardState.GetCommit.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Entry.GetType.spec (GF := GF) (hG := hG))
    (wp_Clone : proto.Clone.spec (GF := GF) (hG := hG))
    (wp_Error : zap.Error.spec (GF := GF) (hG := hG))
    (wp_Fatal : zap.Logger.Fatal.spec (GF := GF) (hG := hG)) :
    raftNode.start.spec (GF := GF) (hG := hG) := by
  intro E γ r rh L
  wp_start as ⟨#Hr, #Hrh, Htok, Hdone, #HT⟩
  ihave #Hr' := Hr
  iunfold isRaftNode at Hr'
  iNamed Hr'
  wp_auto
  simp only [time.Second]
  iunfold isRNTicker at Htki
  icases Htki with ⟨%tc, #Htc, #Htcb, #HtkStop⟩
  iunfold isRaftNodeIfc at Hni
  icases Hni with ⟨%ni, %Hnieq, #HReady, #HAdv, #HTick, #HStop⟩
  subst Hnieq
  iunfold isUnitBag at Hstci
  icases Hstci with ⟨%γst, #Hstb⟩
  wp_auto
  wp_apply wp_fork $$ [Htok Hdone r rh]
  · -- the goroutine
    wp_apply wp_with_defer as %defer defer
    ihave HI : iprop(∃ (L' : List EntryModel) (b : Bool),
        "islead" ∷ islead_ptr ↦ b ∗ "Htok" ∷ rnLoopTok γ L') $$ [islead Htok]
    · iexists L, false
      iframe
    wp_for HI
    rw [method_unfold (t := go.GoType.PointerType raftNode.ty) (m := go!"Ready")]
    wp_auto_lc 4
    rw [method_unfold (t := go.GoType.PointerType raftNodeConfig.ty) (m := go!"Ready")]
    wp_auto
    wp_apply HReady as %rc #Hrc
    wp_apply_core chan.wp_select_blocking_nil
    -- `<-r.ticker.C`: a tick
    iapply BigAndL.bigAndL_cons.2
    isplit
    · icases Htcb with (%Htcn | ⟨%γt, #Htb⟩)
      · iright
        iapply chan.nilClausePre_recv time.Time _ _ Htcn
      ileft
      simp only [chan.blockingClausePre]
      iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tc, γt
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Htb
      iapply bag_recv_au γt tc _ _ $$ [$Hlc1 $Hlc2] Htb
      inext
      iintro %t -
      wp_auto
      ihave HT1 := HT
      imod HT1
      wp_apply wp_tick E γ r $$ [$Hpkg $Hr $HT1]
      wp_for_post
      iframe
      iexists L', b
      iframe
    -- `rd := <-r.Ready()`
    iapply BigAndL.bigAndL_cons.2
    isplit
    · sorry
    -- `<-r.stopped`: return (the deferred `onStop`)
    iapply BigAndL.bigAndL_cons.2
    isplit
    · ileft
      simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, stc, γst
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply is_bag_is_chan $$ Hstb
      iapply bag_recv_au γst stc _ _ $$ [$Hlc1 $Hlc2] Hstb
      inext
      iintro %u -
      wp_auto
      wp_for_post
      wp_apply wp_onStop E γ r $$ [$Hpkg $Hr $Hdone]
      itrivial
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · iapply HΦ
    itrivial

end proof

end EtcdGrove
end Perennial
