/- Lean-first (no Rocq counterpart), 2026-10-13. -/
module

public import Spec.go_etcd_io.raft.v3.node__TransferLeadership
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasNodeR
import all Proof.go_etcd_io.raft.v3.InvNodeChan
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Proof.go_etcd_io.raft.v3.InvBoot
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange
public import Spec.go_etcd_io.raft.v3.NewRawNode
public import Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Perennial.Proof.context
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

## `node.TransferLeadership(ctx, lead, transferee)` (node.go:595), 2026-10-13

From any goroutine: `pb.Message{Type: MsgTransferLeader, From: transferee, To: lead}` onto
`recvc` (`netP`: unstamped, no entries, no context; `netP_local`), which `run` steps as
`RawNode.TransferLeader` does: at a follower forwarded to its leader, at a leader recorded
with a `MsgTimeoutNow` or an append to the transferee. Until stage R7a specified for
`context.Background()`; (2026-10-29, stage U9a) If `n.done` fires, nothing is done. Nothing is promised of the transfer.
(2026-10-16, stage R7a, D10 gap (2)) The context is any `nodeCtx ctx cd` (`InvNodeCtx.lean`); the
`case <-ctx.Done()` returns nothing.
-/

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
private abbrev node.TransferLeadership.specRaw : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (lead transferee : w64)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  -- (2026-10-19, D21 M2r) outside the cluster's no-transfer mode, where leader transfer is off
  -- (`NGhost.xf`; etcd's server, in that mode, never transfers leadership; D22 S-a:
  -- `RaftNames.reNoXfer`, until then the no-snapshot mode's flag)
  γ.raft.reNoXfer = false →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNodeChan γ id n ∗ nodeCtx ctx cd }}
    (App (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"TransferLeadership"))
      (Val #(interface.ok ctx))) (Val #lead)) (Val #transferee))
  {{ RET #(); True }}

end spec

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `recvc <- m` (a local message, `netP_local`); `n.done` never fires, and `ctx` is any
`nodeCtx` (stage R7a): its `Done()` is `nil`, or a context's channel, from which a receive returns
once the context is done (`nodeDone_recv_clause`), and the call returns. (Raft v3.7, stage R5: the message is
`&pb.Message{Type: pb.MsgTransferLeader.Enum(), From: new(transferee), To: new(lead)}`, built
into `msgIn` by `msgIn_of_scalar_struct`; `MsgTransferLeader.Enum()` is a new callee.) -/
private theorem node.TransferLeadership.wp_raw
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    node.TransferLeadership.specRaw (GF := GF) (hG := hG) := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
  intro γ id n lead transferee ctx cd Hns
  wp_start as ⟨#Hnode, #Hctx⟩
  ihave #Hnode' := Hnode
  open_node Hnode'
  wp_auto
  imod termLB_zero (GF := GF) γ.bud with #Hlb
  imod rdCred_zero_upd (GF := GF) γ.raft with Hcr
  imod tickCred_zero (GF := GF) γ.bud with Htc
  rw [show raftpb.MsgTransferLeader = #((W32 13 : raftpb.MessageType)) from rfl]
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 13)
  iintro %pty Hpty
  imod cellRO_alloc $$ Hpty with #cTy
  wp_auto
  imod cellRO_alloc $$ «$v1» with #cFr
  imod cellRO_alloc $$ «$v2» with #cTo
  wp_apply +noauto nodeCtx_Done ctx cd $$ [$Hctx] as %dch #Hd
  wp_auto_lc 3
  imod msgIn_of_scalar_struct «$v0_ptr» pty «$v2_ptr» «$v1_ptr» null null null null null null null
      { (zero_val MessageM) with Type' := W32 13, From' := transferee, To' := lead } ⊤
      $$ [«$v0»] with Hmsg
  · iframe «$v0» cTy cFr cTo
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
        (fun _ => Hns) $$ Hmsg Hlb Hcr Htc
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
  iapply BigAndL.bigAndL_cons.2
  isplit
  · -- `case <-ctx.Done():` returns
    iapply nodeDone_recv_clause ctx cd dch _ _ $$ Hd
    iintro ⟨-, -, -⟩
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

/-- `node.TransferLeadership.spec` from the raw triple (`node`'s names hidden behind the API's). -/
private theorem node.wp_TransferLeadership_impl
    (hT : EtcdGrove.node.TransferLeadership.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.node.TransferLeadership.spec (GF := GF) (hG := hG) := by
  sorry -- PHASE1
  /- PHASE1-OLD
 by
  unfold EtcdGrove.node.TransferLeadership.spec EtcdGrove.Cluster EtcdGrove.isNode EtcdGrove.leaderTransferOn
  intro n γ N id lead transferee ctx cd
  iintro %Φ ⟨#Hinit, #Hnode, #Hctx, Hx⟩ HΦ
  iunfold leaderTransferOn at Hx
  icases Hx with %Hx
  iunfold isNode at Hnode
  icases Hnode with ⟨%γn, %Hf, #Hrn, -⟩
  obtain ⟨Hγr, -⟩ := Hf
  iapply (hT γn id n lead transferee ctx cd (by rw [Hγr]; exact Hx)) $$ []
  · iframe Hinit Hrn Hctx
  iexact HΦ
  -/

end wrap

end ApiImpl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem node.TransferLeadership.wp_proof
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    node.TransferLeadership.spec (GF := GF) (hG := hG) :=
  ApiImpl.node.wp_TransferLeadership_impl (node.TransferLeadership.wp_raw wp_MessageType_Enum)

end proof

end EtcdGrove
end Perennial
