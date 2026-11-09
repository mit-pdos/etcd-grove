/-
## `raft.responseToReadIndexReq(req, readIndex)` (internal)

**Users.** `stepLeader`'s heartbeat-response arm (`raft.go:1622`), `sendMsgReadIndexResponse`
(`:2154`, `:2167`). **Proof sketch.** A local request (from no one or the node: one entry, its
context): a read state `(context, index)` queued (`readStates`; its `readState γ c i` from
`readConfirmed`, handed out in a `Ready`), and an empty message back (`To = 0`, which the callers do
not send). A forwarded one: a `MsgReadIndexResp` to the sender at the index, with the request's
entries (its `msgJust`: the read confirmed at `i`). **Changes** (from `specs-ref`'s
`raft__responseToReadIndexReq.lean`): over the opened struct and `readConfirmed`. **Margin.** The
view and log are unchanged.
-/
module

public import Spec.go_etcd_io.raft.v3.ApiCore

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (internal) Answers a confirmed read: a local read state, or a response to its sender. -/
def raft.responseToReadIndexReq.spec : Prop :=
  ∀ (r : Loc) (γ : Cluster) (id : w64) (o : CoreOpen) (rq : Loc) (dq : DFrac) (m : Msg) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftOpen r γ id o ∗ coreInv r γ id o ∗ msgPts rq dq m ∗ readConfirmed γ m i ∗
      ⌜(m.src = W64 0 ∨ m.src = id) → m.entries ≠ []⌝ }}
    (App (App (Val (r @!! go.GoType.PointerType go_etcd_io.raft.v3.raft.ty @!! go!"responseToReadIndexReq")) (Val #rq)) (Val #i))
  {{ (p : Loc), RET #p; ∃ o' rm, raftOpen r γ id o' ∗ coreInv r γ id o' ∗ ⌜o'.view = o.view⌝ ∗
      msgPts rq dq m ∗ msgPts p (DFrac.own 1) rm ∗
      (⌜(m.src = W64 0 ∨ m.src = id) ∧ rm.to = W64 0⌝ ∨
       (⌜rm.type = MsgReadIndexResp ∧ rm.to = m.src ∧ rm.index = i ∧ rm.entries = m.entries⌝ ∗
        msgJust r γ id rm)) }}

end spec
end Raft
end EtcdGrove
end Perennial
