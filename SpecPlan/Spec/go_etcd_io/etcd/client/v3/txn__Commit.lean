/-
`(*clientv3.txn).Commit` (`client/v3/txn.go`).

Users: `client/v3/concurrency` (`mutex.go:83` `tryAcquire`, `election.go:69` `Campaign`, `stm.go:203`
`commit`), `experimental/recipes` (`key.go:91` `putNewKV`, `queue.go`), leasing (`leasing/txn.go`),
Kubernetes' store (`etcd3/store.go` `Create`/`GuaranteedUpdate`/`Delete`: `If(ModRevision(key) =
rv).Then(OpPut(...)).Else(OpGet(key))`) and compactor (`etcd3/compact.go`: `If(Version(key) =
t).Then(OpPut(key, "")).Else(OpGet(key))`), the examples (`txnlin/linkvtxn.go:935` `callTxn`).
Snippets: `clientv3kv/txn.go`.

Proof sketch: locks; allocates `&pb.TxnRequest{Compare: cmps, Success: sus, Failure: fas}`
(`txnReqOwn_unfold`, the slices' messages owned by the `txn` at a fraction), then
`RemoteKV.TxnTriple` of `t.kv.remote` with `t.callOpts` (the client's, not repeatable) and the
caller's update (`□?` as given); `ContextError.spec` on the error; unlocks, the `txnAt` back.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/txn__Commit.lean`: restated over `txnAt` and the model's requests; any transaction (with leases, `IgnoreLease`, nested, read-only: a read-only one takes a persistent update, as the server answers it from the read index or, serializable, from a member's view: `issues/etcd-txn-empty-serializable.md` in the model).

verify-round: the `TxnRequest` and its `RequestOp`s are built at `own 1` and persisted to the one fraction `txnReqOwn r DFrac.discard t` takes by `protoRest_persist` (A1-provability F6); `Txn.CommitTriple` takes the state predicate as a parameter (`txnAt_intro`, A1-completeness F2).

Margin: on success the code also guarantees the reply's header names the member that
answered (`MemberId`, `RaftTerm`), not modelled; on an indefinite error the code may still have
applied the put (the update fires later or not at all), which is all the spec says.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `t.Commit` of a `*txn` (`kv.Txn`'s) meets the `Txn` contract's `Commit` (`Txn.CommitTriple`). -/
def txn.Commit.spec : Prop :=
  ∀ (t : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface),
  Txn.CommitTriple (GF := GF) (t @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Commit")
    (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty) #t) γ who ctx

end spec

end ClientV3
end EtcdGrove
end Perennial
