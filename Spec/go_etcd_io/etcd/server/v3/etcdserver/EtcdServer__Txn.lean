/-
## `(*EtcdServer).Txn(ctx, r)`

**Users.** The gRPC KV handler (`api/v3rpc/key.go:130`, after `checkTxnRequest` at the server's
`--max-txn-ops`, which bounds the nesting: `txnChecked`, and the depth, `irr-depth.md`), the
grpc-proxy's adapter. Snippets: `examples/specreq/etcdserverreq/kv.go` (`ReqTxnReadOnly`,
`ReqTxnCAS`).

**Proof sketch.** `txn.IsTxnReadonly(r)` (3b: `t.readonly`). Read-only: as `Range.spec` (the
registry's ticket; the read index unless `txn.IsTxnSerializable(r)`, 3b: `t.serializable`; then
`doSerialize` with `chk` = `apply.CheckTxnAuth` (3a: the permission of `RequestOp.txn`'s
`perms` and `leases` at the auth store's state) and `get` = `txn.Txn(...)` (3b: `TxnRun` at the
member's store; a read-only run commits nothing). A write: as `Put.spec` (`raftRequest` at `.req
(.txn t)`, its depth premise from this one's; the type assertion `resp.(*pb.TxnResponse)`).

**Changes.** The old spec (`specs-ref`'s `EtcdServer__Txn.lean`: `txnPermit`, a depth premise of a
writing transaction) restated as `Put` and `Range`: one spec for both modes, the update persistent
exactly for a read (`□?`), the depth premise kept (`irr-depth.md`: the receiver's need, not v3rpc's
budget), `txnChecked` the gRPC layer's validation (2a's).

**Margin.** As `Range` and `Put` (the depth and `txnChecked` premises are `IrrBody.wf`'s). A compare-only transaction is answered from a member's possibly
stale store (`issues/etcd-txn-empty-serializable.md`: W0's model has it).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.ApiReq

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace EtcdServer

open Iris Iris.BI EtcdModel EtcdWire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`s.Txn(ctx, r)`**: the transaction `t`: read-only, as `Range` (persistent update, the linearizable or serializable read); a write, as `Put` (through raft). -/
def EtcdServer.Txn.spec : Prop :=
  ∀ (s : Loc) (γ : Cluster) (ctx : GoInterface) (p tls : Principal) (r : Loc) (dq : DFrac) (t : TxnReq),
  SrvCallTriple (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.EtcdServer.ty @!! go!"Txn")) (Val #ctx)) (Val #r))
    iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗ isServer s γ ∗
        Context.ctxOk ctx ∗ reqCtxOk ctx ∗ reqPrin ctx p tls ∗ threadTok ∗ txnReqOwn r dq t ∗ ⌜txnChecked t⌝ ∗ ⌜(Req.txn t).isRead = false → txnMsgDepth t + 1 ≤ 10000⌝)
    iprop(threadTok ∗ txnReqOwn r dq t) γ p tls (.txn t) (Req.txn t).isRead (ClientV3.txnReply)

end spec
end EtcdServer
end EtcdGrove
end Perennial
