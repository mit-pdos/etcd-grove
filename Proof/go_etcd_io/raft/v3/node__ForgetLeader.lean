/- Lean-first (no Rocq counterpart), 2026-10-13. -/
module

public import Spec.go_etcd_io.raft.v3.node__ForgetLeader
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasNodeR
public import Spec.go_etcd_io.raft.v3.node__step
public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.InvApplyConf
public import Proof.go_etcd_io.raft.v3.InvBoot
public import Spec.go_etcd_io.raft.v3.RawNode__ProposeConfChange
public import Spec.go_etcd_io.raft.v3.NewRawNode
public import Proof.go_etcd_io.raft.v3.InvNodeCtx
public import Proof.go_etcd_io.raft.v3.InvNodeChan
public import Perennial.Proof.context
import all Proof.go_etcd_io.raft.v3.InvNode
import Proof.go_etcd_io.raft.v3.InvApi

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The raw triple (internal: private to this file) -/

/-! Lean-first (no Rocq counterpart).

## `node.ForgetLeader(ctx)` (node.go:604), 2026-10-13

From any goroutine: `step` of `pb.Message{Type: MsgForgetLeader}` (`netP_local`), which
`run` steps as `RawNode.ForgetLeader` does: a follower forgets its leader. Until stage R7a
specified for `context.Background()`; the error said only whether the message reached `run`.
(2026-10-16, stage R7a, D10 gap (2)) The context is any `nodeCtx ctx cd` (`InvNodeCtx.lean`:
`Done()` nil, or Perennial's `isContext`), and the error `nodeErr cd err`: `nil`, raft's
`ErrStopped`, or the context's once its `Done()` fired (`ctxErr`). -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the header above. -/
private abbrev node.ForgetLeader.specRaw : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNodeChan γ id n ∗ nodeCtx ctx cd }}
    (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"ForgetLeader"))
      (Val #(interface.ok ctx)))
  {{ (err : GoInterface), RET #err; nodeErr cd err }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `step` of the literal message, a local one (`netP_local`). (Raft v3.7, stage R5: the message
is `&pb.Message{Type: pb.MsgForgetLeader.Enum()}`, built into `msgIn` by
`msgIn_of_scalar_struct`; `MsgForgetLeader.Enum()` is a new callee. Stage R7a: any `nodeCtx`, the
error `nodeErr`.) -/
private theorem node.ForgetLeader.wp_raw
    (wp_node_step : node.step.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    node.ForgetLeader.specRaw (GF := GF) (hG := hG) := by
  intro γ id n ctx cd
  wp_start as ⟨#Hnode, #Hctx⟩
  wp_auto
  imod termLB_zero (GF := GF) γ.bud with #Hlb
  imod rdCred_zero_upd (GF := GF) γ.raft with Hcr
  imod tickCred_zero (GF := GF) γ.bud with Htc
  rw [show raftpb.MsgForgetLeader = #((W32 23 : raftpb.MessageType)) from rfl]
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 23)
  iintro %pty Hpty
  imod cellRO_alloc $$ Hpty with #cTy
  wp_auto
  imod msgIn_of_scalar_struct «$a1_ptr» pty null null null null null null null null null
      { (zero_val MessageM) with Type' := W32 23 } ⊤ $$ [«$a1»] with Hmsg
  · iframe «$a1» cTy
    repeat (isplitr; · iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩)
    iunfold cellRO; ileft; ipureintro; exact ⟨rfl, rfl⟩
  wp_apply wp_node_step γ id n _ ctx cd $$ [Hmsg Hcr Htc]
  · iframe Hnode Hctx
    unfold stepP
    ileft
    iapply netP_local γ id _ _ (.inr (.inl rfl)) rfl rfl rfl rfl
        (by intro h; exfalso; revert h; first | decide | simp [MsgTransferLeader, MsgForgetLeader, MsgUnreachable, MsgSnapStatus]) $$ Hmsg Hlb Hcr Htc
  iintro %err #Herr
  wp_auto
  iapply HΦ
  iexact Herr

end proof

/-! ## The spec, from the raw triple -/

namespace ApiImpl

section wrap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `node.ForgetLeader.spec` from the raw triple (`node`'s names hidden behind the API's). -/
private theorem node.wp_ForgetLeader_impl
    (hS : EtcdGrove.node.ForgetLeader.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.node.ForgetLeader.spec (GF := GF) (hG := hG) := by
  unfold EtcdGrove.node.ForgetLeader.spec EtcdGrove.Cluster EtcdGrove.isNode
  intro n γ N id ctx cd
  iintro %Φ ⟨#Hinit, #Hnode, #Hctx⟩ HΦ
  iunfold isNode at Hnode
  icases Hnode with ⟨%γn, -, #Hrn, -⟩
  iapply (hS γn id n ctx cd) $$ []
  · iframe Hinit Hrn Hctx
  iexact HΦ

end wrap

end ApiImpl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem node.ForgetLeader.wp_proof
    (wp_node_step : node.step.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    node.ForgetLeader.spec (GF := GF) (hG := hG) :=
  ApiImpl.node.wp_ForgetLeader_impl (node.ForgetLeader.wp_raw wp_node_step wp_MessageType_Enum)

end proof

end EtcdGrove
end Perennial
