/- Lean-first (no Rocq counterpart), 2026-10-13. -/
module

public import Spec.go_etcd_io.raft.v3.node__ReportSnapshot
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasNodeR
import all Proof.go_etcd_io.raft.v3.InvNode
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Proof.go_etcd_io.raft.v3.InvBoot
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange
public import Spec.go_etcd_io.raft.v3.NewRawNode

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

/-- `recvc <- m` (a local message, `netP_local`); `n.done` never fires. (Raft v3.7, stage R5:
the message is `&pb.Message{Type: pb.MsgSnapStatus.Enum(), From: new(id), Reject: new(rej)}`,
built into `msgIn` by `msgIn_of_scalar_struct`; `MsgSnapStatus.Enum()` is a new callee.) -/
theorem node.ReportSnapshot.wp_proof
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    node.ReportSnapshot.spec (GF := GF) (hG := hG) := by
  intro γ id n to st
  wp_start as #Hnode
  ihave #Hnode' := Hnode
  open_node Hnode'
  imod termLB_zero (GF := GF) γ.bud with #Hlb
  imod rdCred_zero_upd (GF := GF) γ.raft with Hcr
  imod tickCred_zero (GF := GF) γ.bud with Htc
  wp_auto_lc 3
  rw [show raftpb.MsgSnapStatus = #((W32 11 : raftpb.MessageType)) from rfl]
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 11)
  iintro %pty Hpty
  imod cellRO_alloc $$ Hpty with #cTy
  wp_auto
  imod cellRO_alloc $$ «$v1» with #cFr
  imod cellRO_alloc $$ «$v2» with #cRj
  imod msgIn_of_scalar_struct «$v0_ptr» pty null «$v1_ptr» null null null null null «$v2_ptr» null
      { (zero_val MessageM) with Type' := W32 11, From' := to, Reject' := decide (st = W64 2) } ⊤
      $$ [«$v0»] with Hmsg
  · iframe «$v0» cTy cFr cRj
    repeat (isplitr; · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩)
    iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
  wp_apply_core chan.wp_select_blocking_nil
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
    iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance,
      nv.recvc', γ.recvc, _
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · iapply isHandshake_isChan $$ Hrecvc
    iapply handshake_send_au γ.recvc nv.recvc' _ (netP γ id) iprop(True)
      $$ [$Hlc1 $Hlc2 $Hlc3] Hrecvc [Hmsg Hcr Htc]
    · iapply netP_local γ id _ _ (by first | exact .inl rfl | exact .inr (.inl rfl) | exact .inr (.inr (.inl rfl)) | exact .inr (.inr (.inr rfl))) rfl rfl rfl rfl
        (by intro h; exfalso; revert h; first | decide | simp [MsgTransferLeader, MsgForgetLeader, MsgUnreachable, MsgSnapStatus]) $$ Hmsg Hlb Hcr Htc
    inext
    iintro -
    wp_auto
    iapply HΦ
    itrivial
  iapply BigAndL.bigAndL_cons.2
  isplit
  · ileft
    simp only [chan.blockingClausePre]
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
