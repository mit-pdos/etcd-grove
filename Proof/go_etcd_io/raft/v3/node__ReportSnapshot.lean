/- Lean-first (no Rocq counterpart), 2026-10-13. -/
module

public import Spec.go_etcd_io.raft.v3.node__ReportSnapshot
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasNodeR
import all Proof.go_etcd_io.raft.v3.InvNodeChan
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Proof.go_etcd_io.raft.v3.InvBoot
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange
public import Spec.go_etcd_io.raft.v3.NewRawNode
import all Proof.go_etcd_io.raft.v3.InvNode
import Proof.go_etcd_io.raft.v3.InvApi
import Proof.go_etcd_io.raft.v3.InvApiView

@[expose] public section

noncomputable section


namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The raw triple (internal: private to this file)

What the proof over raft's internals shows, from which the wrapper (below) derives the spec. Its documentation, as when it was the spec (until 2026-10-28):
-/

/-! Lean-first (no Rocq counterpart).

## `node.ReportSnapshot(id, status)` (node.go:586), 2026-10-13

From any goroutine: `pb.Message{Type: MsgSnapStatus, From: id, Reject: status ==
SnapshotFailure}` onto `recvc` (`netP_local`), which `run` steps as
`RawNode.ReportSnapshot` does: a leader's `Progress` of `id` only. (2026-10-29, stage U9a) If `n.done` fires, nothing is done.
-/

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
private abbrev node.ReportSnapshot.specRaw : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (to : w64) (st : SnapshotStatus),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNodeChan γ id n }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ReportSnapshot")) (Val #to))
      (Val #st))
  {{ RET #(); True }}

end spec

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `recvc <- m` (a local message, `netP_local`); (2026-10-29, stage U9a) If `n.done` fires, nothing is done. (Raft v3.7, stage R5:
the message is `&pb.Message{Type: pb.MsgSnapStatus.Enum(), From: new(id), Reject: new(rej)}`,
built into `msgIn` by `msgIn_of_scalar_struct`; `MsgSnapStatus.Enum()` is a new callee.) -/
private theorem node.ReportSnapshot.wp_raw
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    node.ReportSnapshot.specRaw (GF := GF) (hG := hG) := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
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
    · iapply ownBroadcastChan_is_chan _ _ _ _ $$ Hdone
    -- (2026-10-29, stage U9a) the node stopped: nothing done
    iapply node_done_recv_au γ nv.done' _ $$ Hdone
    iintro -
    wp_auto
    iapply HΦ
    itrivial
  iapply BigAndL.bigAndL_nil.2
  itrivial
  -/

end proof

/-! ## The spec, from the raw triple -/

namespace ApiImpl

section wrap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `node.ReportSnapshot.spec` from the raw triple (`node`'s names hidden behind the API's). -/
private theorem node.wp_ReportSnapshot_impl
    (hR : EtcdGrove.node.ReportSnapshot.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.node.ReportSnapshot.spec (GF := GF) (hG := hG) := by
  unfold EtcdGrove.node.ReportSnapshot.spec EtcdGrove.Cluster EtcdGrove.isNode
  intro n γ N id to status
  iintro %Φ ⟨#Hinit, #Hnode⟩ HΦ
  iunfold isNode at Hnode
  icases Hnode with ⟨%γn, -, #Hrn, -⟩
  iapply (hR γn id n to status) $$ []
  · iframe Hinit Hrn
  iexact HΦ

end wrap

end ApiImpl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem node.ReportSnapshot.wp_proof
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    node.ReportSnapshot.spec (GF := GF) (hG := hG) :=
  ApiImpl.node.wp_ReportSnapshot_impl (node.ReportSnapshot.wp_raw wp_MessageType_Enum)

end proof

end EtcdGrove
end Perennial
