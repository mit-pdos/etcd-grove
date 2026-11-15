/-
## `WarnOfExpensiveReadOnlyTxnRequest(lg, d, now, r, txnResponse, err)` (`util.go`)

**Users.** `EtcdServer.Txn`'s deferred warning for a read-only transaction (`v3_server.go:359`: its
request, the reply, `nil`, or the partly filled response after a context error). Snippet: none.

**Proof sketch.** `pb.NewLoggableTxnRequest(r)` (3h's: `stringerAt s` lent from the request's share, given back by
`stringerAt s -∗ msgAt …`; its depth premise from 3h's `txnReqOwn_msgAt` and `holds_depth_txn`,
`depth c ≤ txnMsgDepth t`, and this spec's premise); past the duration,
`isNil`, the loop over `Responses` (each a range response, its message `nil` or a reply:
`GetResponseRange`, `GetKvs`, 3h's getters), `proto.Size` (a read-only transaction's response is at
most four levels deep), `warnOfExpensiveGenericRequest`.

**Changes.** The old spec's `roTxnRespRd` kept as `roTxnResp`, beside a full reply.
Recheck (RR4): premise `txnMsgDepth t < Proto.depthMax`, what `NewLoggableTxnRequest` needs (its
text marshaling recurses per level); its caller's transaction is read-only, so `txnMsgDepth t ≤ 3`
(only ranges in both branches: `opMsgDepth (.range _) = 2`). The premise is the need, not
`t.readonly`, which would be stronger.
**Margin.** None.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Txn

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

/-- `WarnOfExpensiveReadOnlyTxnRequest(...)` with the request and a read-only transaction's reply
(`some m`, every response a range), or `nil` or a partly filled one (`none`): returns, both given
back. -/
def WarnOfExpensiveReadOnlyTxnRequest.spec : Prop :=
  ∀ (lg : Loc) (d : time.Duration) (now : time.Time) (rt : Loc) (dqr : DFrac) (t : TxnReq)
    (resp : Loc) (dq : DFrac) (mo : Option TxnRespM) (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.txn ∗ Zap.isLogger lg ∗ txnReqOwn rt dqr t ∗
      ⌜EtcdServerPb.txnMsgDepth t < Proto.depthMax⌝ ∗
      (match mo with
       | some m => iprop(txnRespOwn resp dq m ∗ ⌜∀ ro ∈ m.responses, ∃ rm, ro = .range rm⌝)
       | none => iprop(⌜resp = null⌝ ∨ roTxnResp resp)) }}
    (App (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.txn.WarnOfExpensiveReadOnlyTxnRequest)) (Val #lg)) (Val #d)) (Val #now)) (Val #rt)) (Val #resp)) (Val #err))
  {{ RET #(); txnReqOwn rt dqr t ∗
      (match mo with
       | some m => iprop(txnRespOwn resp dq m ∗ ⌜∀ ro ∈ m.responses, ∃ rm, ro = .range rm⌝)
       | none => iprop(⌜resp = null⌝ ∨ roTxnResp resp)) }}

end spec
end Txn
end EtcdGrove
end Perennial
