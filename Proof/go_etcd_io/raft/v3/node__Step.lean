/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.node__Step
public import Proof.ReceiptTactics
public import Spec.go_etcd_io.raft.v3.IsLocalMsg
public import Spec.go_etcd_io.raft.v3.IsLocalMsgTarget
public import Spec.go_etcd_io.raft.v3.node__step
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetType
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetFrom
public import Proof.go_etcd_io.raft.v3.LemmasNodeR
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
import Proof.go_etcd_io.raft.v3.InvApiDyn

@[expose] public section

noncomputable section


namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

/-! ## The raw triple (internal: private to this file)

What the proof over raft's internals shows, from which the wrapper (below) derives the spec. Its documentation, as when it was the spec (until 2026-10-28):
-/

/-! Lean-first (no Rocq counterpart).

## `node.Step(ctx, m)` (node.go:473)

A message from the network, from any goroutine: `step` of it, on `recvc`, which `run` steps
as `RawNode.Step` does (`netP`: what `RawNode.Step` takes, and a term within the budget).
A local message not from a local target is ignored (since 2026-10-13 `netP` admits two
local types, `MsgUnreachable` and `MsgSnapStatus`, the reports `node.go` itself puts on
`recvc`: through `Node.Step` they are ignored unless from a local target).
Since 2026-10-10 also a proposal forwarded by a peer (`fwdP`, `stepP`): a follower's
`Ready` holds the proposals it forwards to the leader (each entry's data deposited by the
proposing node), which `step` hands to `run` on `propc`.
Until stage R7a specified for `context.Background()`.
(2026-10-16, stage R7a, D10 gap (2)) The context is any `nodeCtx ctx cd` (`InvNodeCtx.lean`:
`Done()` nil, or Perennial's `isContext`), and the error `nodeErr cd err`: `nil`, raft's
`ErrStopped`, or the context's once its `Done()` fired (`ctxErr`).

raft v3.7 (2026-10-16, stage R5): `m` is a `*pb.Message` (`ml`), handed to `run` for good
(`stepP`: `netP`'s `msgIn ml □`, `fwdP`'s `msgIn ml 1`); a `nil` one is an error, which `stepP`
excludes.
-/

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
private abbrev node.Step.specRaw : Prop :=
  ∀ (γ : NodeNames) (id : w64) (n : Loc) (ml : Loc)
    (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNodeChan γ id n ∗
      nodeCtx ctx cd ∗
      -- (2026-10-29, stage U7) for a time receipt, which `Step` takes from a Go step of its own
      ⌜ml ≠ null⌝ ∗ (⧗ 1 -∗ stepP γ id ml) }}
    (App (App (Val (n @!! go.GoType.PointerType node.ty @!! go!"Step"))
      (Val #(interface.ok ctx))) (Val #ml))
  {{ (err : GoInterface), RET #err; nodeErr cd err }}

end spec

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A local message from a remote sender is dropped; anything else goes to `step`. (Raft v3.7,
stage R5: `m` a pointer, not `nil` (`stepP`'s `msgIn`, so the `nil` check's error is
unreachable); its type and sender read by `m.GetType()`/`m.GetFrom()`, new callees, over the
message `stepP_split` opens. Stage R7a: any `nodeCtx`, the error `nodeErr`, `nil` for a dropped
message.) -/
private theorem node.Step.wp_raw
    (wp_IsLocalMsg : IsLocalMsg.spec (GF := GF) (hG := hG))
    (wp_IsLocalMsgTarget : IsLocalMsgTarget.spec (GF := GF) (hG := hG))
    (wp_node_step : node.step.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG)) :
    node.Step.specRaw (GF := GF) (hG := hG) := by
  intro γ id n m ctx cd
  wp_start as ⟨#Hnode, #Hctx, %Hnn, Hstep⟩
  -- (2026-10-29, stage U7) the receipt, at the `nil` check's comparison
  repeat (
    fail_if_success wp_bind (App (Val (GoInstruction (GoOp _ _))) (Val _))
    first | wp_pure | wp_load | wp_store | wp_alloc_auto)
  wp_bind (App (Val (GoInstruction (GoOp _ _))) (Val _))
  iapply wp_go_step_receipt'
  case hv => first | rfl | simp [val.isPanic] | decide
  inext
  iintro Hr -
  ihave Hstep := Hstep $$ Hr
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  icases stepP_split γ id m $$ Hstep with ⟨%dqe, %st, Hm, %Hty, Hclose⟩
  wp_apply wp_GetType.1 $$ [Hm] as Hm
  · iexact Hm
  wp_apply wp_IsLocalMsg st.msg.Type' Hty as %b -
  cases b
  · wp_auto
    wp_apply wp_node_step γ id n m ctx cd $$ [$Hnode $Hctx Hm Hclose]
    · iapply Hclose $$ Hm
    iintro %err #Herr
    wp_auto
    iapply HΦ
    iexact Herr
  · wp_auto
    wp_apply wp_GetFrom.1 $$ [Hm] as Hm
    · iexact Hm
    wp_apply wp_IsLocalMsgTarget st.msg.From'
    wp_if_destruct
    · wp_apply wp_node_step γ id n m ctx cd $$ [$Hnode $Hctx Hm Hclose]
      · iapply Hclose $$ Hm
      iintro %err #Herr
      wp_auto
      iapply HΦ
      iexact Herr
    · iapply HΦ
      iapply nodeErr_nil

end proof

/-! ## The spec, from the raw triple -/

namespace ApiImpl

section wrap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `node.Step.spec` from the raw triple (`node`'s names hidden behind the API's). -/
private theorem node.wp_Step_impl
    (hS : EtcdGrove.node.Step.specRaw (GF := GF) (hG := hG)) :
    EtcdGrove.node.Step.spec (GF := GF) (hG := hG) := by
  unfold EtcdGrove.node.Step.spec EtcdGrove.Cluster EtcdGrove.isNode EtcdGrove.stepIn
  intro n γ N id ml ctx cd
  iintro %Φ ⟨#Hinit, #Hnode, #Hctx, Hin⟩ HΦ
  iunfold isNode at Hnode
  icases Hnode with ⟨%γn, %Hf, #Hrn, -⟩
  iapply (hS γn id n ml ctx cd) $$ [Hin]
  · iframe Hinit Hrn Hctx
    iunfold stepIn at Hin
    icases Hin with ⟨%Hnn, Hin⟩
    isplitr; · ipureintro; exact Hnn
    iapply Hin
    ipureintro; exact Hf
  iexact HΦ

end wrap

end ApiImpl

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem node.Step.wp_proof
    (wp_IsLocalMsg : IsLocalMsg.spec (GF := GF) (hG := hG))
    (wp_IsLocalMsgTarget : IsLocalMsgTarget.spec (GF := GF) (hG := hG))
    (wp_node_step : node.step.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Message.GetType.spec (GF := GF) (hG := hG))
    (wp_GetFrom : raftpb.Message.GetFrom.spec (GF := GF) (hG := hG)) :
    node.Step.spec (GF := GF) (hG := hG) :=
  ApiImpl.node.wp_Step_impl (node.Step.wp_raw wp_IsLocalMsg wp_IsLocalMsgTarget wp_node_step wp_GetType wp_GetFrom)

end proof

end EtcdGrove
end Perennial
