/- Lean-first (no Rocq counterpart), 2026-10-13. -/
module

public import Spec.go_etcd_io.raft.v3.node__ApplyConfChange
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__AsV2
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeV2__AsV2

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem node.ApplyConfChange.wp_proof
    (wp_ConfChange_AsV2 : raftpb.ConfChange.AsV2.spec (GF := GF) (hG := hG))
    (wp_ConfChangeV2_AsV2 : raftpb.ConfChangeV2.AsV2.spec (GF := GF) (hG := hG)) :
    node.ApplyConfChange.spec (GF := GF) (hG := hG) := by
  intro γ id n c o Hnoop
  wp_start as ⟨#Hnode, Hc⟩
  ihave #Hnode' := Hnode
  open_node Hnode'
  rcases o with m | m
  · simp only [ownCCI, ownCCV1]
    icases Hc with ⟨%v, %Hcv, %Hvm, -⟩
    subst Hcv
    obtain ⟨Hty, Hnid, -⟩ := Hvm
    wp_auto
    wp_apply +noauto wp_ConfChange_AsV2 as %v2 ⟨%Hv2, Hch⟩
    imod ownSlice_persist $$ Hch with #Hch
    ihave HP : confcP γ v2 $$ []
    · unfold confcP
      iexists _
      iframe Hch
      ipureintro
      rw [Hv2.1, Hty, Hnid]; exact Hnoop
    wp_auto_lc 3
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists raftpb.ConfChangeV2, inferInstance, inferInstance, inferInstance, inferInstance,
        nv.confc', γ.confc, _
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iapply isHandshake_isChan $$ Hconfc
      iapply handshake_send_au γ.confc nv.confc' _ (confcP γ) iprop(True)
        $$ [$Hlc1 $Hlc2 $Hlc3] Hconfc HP
      inext
      iintro -
      wp_auto_lc 2
      wp_apply_core chan.wp_select_blocking
      iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.blockingClausePre]
        iexists raftpb.ConfState, inferInstance, inferInstance, inferInstance, inferInstance,
          nv.confstatec', γ.confstatec
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply isHandshake_isChan $$ Hconfstatec
        iapply handshake_receive_au γ.confstatec nv.confstatec' (confstateP γ) iprop(True) _
          $$ [$Hlc1 $Hlc2] Hconfstatec []
        · itrivial
        inext
        iintro %csv Hcs
        wp_auto
        iapply HΦ
        iframe
      iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.done', γ.done
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply isHandshake_isChan $$ Hdone
        iapply handshake_false_recv_au γ.done nv.done' $$ [$Hlc1 $Hlc2] Hdone
      iapply BigAndL.bigAndL_nil.2
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.done', γ.done
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply isHandshake_isChan $$ Hdone
      iapply handshake_false_recv_au γ.done nv.done' $$ [$Hlc1 $Hlc2] Hdone
    iapply BigAndL.bigAndL_nil.2
    itrivial
  · simp only [ownCCI, ownCCV2]
    icases Hc with ⟨%v, %Hcv, %Htr, #Hch, -⟩
    subst Hcv
    wp_auto
    wp_apply +noauto wp_ConfChangeV2_AsV2
    ihave HP : confcP γ v $$ []
    · unfold confcP
      iexists _
      iframe Hch
      ipureintro
      rw [Htr]; exact Hnoop
    wp_auto_lc 3
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists raftpb.ConfChangeV2, inferInstance, inferInstance, inferInstance, inferInstance,
        nv.confc', γ.confc, _
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      isplitr
      · iapply isHandshake_isChan $$ Hconfc
      iapply handshake_send_au γ.confc nv.confc' _ (confcP γ) iprop(True)
        $$ [$Hlc1 $Hlc2 $Hlc3] Hconfc HP
      inext
      iintro -
      wp_auto_lc 2
      wp_apply_core chan.wp_select_blocking
      iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.blockingClausePre]
        iexists raftpb.ConfState, inferInstance, inferInstance, inferInstance, inferInstance,
          nv.confstatec', γ.confstatec
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply isHandshake_isChan $$ Hconfstatec
        iapply handshake_receive_au γ.confstatec nv.confstatec' (confstateP γ) iprop(True) _
          $$ [$Hlc1 $Hlc2] Hconfstatec []
        · itrivial
        inext
        iintro %csv Hcs
        wp_auto
        iapply HΦ
        iframe
      iapply BigAndL.bigAndL_cons.2
      isplit
      · simp only [chan.blockingClausePre]
        iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.done', γ.done
        isplitr
        · ipureintro; rfl
        isplitr
        · iapply isHandshake_isChan $$ Hdone
        iapply handshake_false_recv_au γ.done nv.done' $$ [$Hlc1 $Hlc2] Hdone
      iapply BigAndL.bigAndL_nil.2
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · simp only [chan.blockingClausePre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, nv.done', γ.done
      isplitr
      · ipureintro; rfl
      isplitr
      · iapply isHandshake_isChan $$ Hdone
      iapply handshake_false_recv_au γ.done nv.done' $$ [$Hlc1 $Hlc2] Hdone
    iapply BigAndL.bigAndL_nil.2
    itrivial

end proof

end EtcdGrove
end Perennial
