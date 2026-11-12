/-
`(*clientv3.txn).Then` (`client/v3/txn.go`).

Users: `client/v3/concurrency` (`mutex.go:83` `tryAcquire`, `election.go:69` `Campaign`, `stm.go:203`
`commit`), `experimental/recipes` (`key.go:91` `putNewKV`, `queue.go`), leasing (`leasing/txn.go`),
Kubernetes' store (`etcd3/store.go` `Create`/`GuaranteedUpdate`/`Delete`: `If(ModRevision(key) =
rv).Then(OpPut(...)).Else(OpGet(key))`) and compactor (`etcd3/compact.go`: `If(Version(key) =
t).Then(OpPut(key, "")).Else(OpGet(key))`), the examples (`txnlin/linkvtxn.go:935` `callTxn`).
Snippets: `clientv3kv/txn.go`.

Proof sketch: locks; the flags (premise); for each `Op` of `ops` (`opsAt`): `Op.isWrite.spec`,
`Op.toRequestOp.spec` (premise `toReqOps os = some rs`: no zero `Op` at any depth), appended to
`t.sus`; unlocks.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/txn__Then.lean`: restated over `txnAt` and the model's requests; a nested transaction (`OpTxn`) is now admitted in `Then`/`Else` (the old builder model excluded it); otherwise unchanged.

verify-round: premise `OpM.anyEmptyEnd os = false` (A1-provability F5); `Txn.ThenTriple` takes the state predicate as a parameter (`txnAt` by default; `txnAt_intro`, A1-completeness F2).

Margin: none.
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

/-- `t.Then` of a `*txn` (`kv.Txn`'s) meets the `Txn` contract's `Then` (`Txn.ThenTriple`). -/
def txn.Then.spec : Prop :=
  ∀ (t : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface),
  Txn.ThenTriple (GF := GF) (t @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"Then")
    (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty) #t) γ who ctx

end spec

end ClientV3
end EtcdGrove
end Perennial
