/-
`(*clientv3.txn).If` (`client/v3/txn.go`).

Users: `client/v3/concurrency` (`mutex.go:83` `tryAcquire`, `election.go:69` `Campaign`, `stm.go:203`
`commit`), `experimental/recipes` (`key.go:91` `putNewKV`, `queue.go`), leasing (`leasing/txn.go`),
Kubernetes' store (`etcd3/store.go` `Create`/`GuaranteedUpdate`/`Delete`: `If(ModRevision(key) =
rv).Then(OpPut(...)).Else(OpGet(key))`) and compactor (`etcd3/compact.go`: `If(Version(key) =
t).Then(OpPut(key, "")).Else(OpGet(key))`), the examples (`txnlin/linkvtxn.go:935` `callTxn`).
Snippets: `clientv3kv/txn.go`.

Proof sketch: `txnAt` of the `*txn`: its fields under `t.mu`'s lock invariant. Locks `t.mu`; the flags
(premise: all false, else it panics); for each `Cmp` of `cs` (`cmpsAt`): `Cmp.Clone.spec` (a fresh
copy, `cmpAt _ m`), `Cmp.GetCompare.spec` (a zero `Cmp` gets a zero `Compare`), appended to
`t.cmps` (slice append, Perennial); unlocks.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/txn__If.lean`: restated over `txnAt` and the model's requests; otherwise unchanged.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Api

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

/-- `t.If` of a `*txn` (`kv.Txn`'s) meets the `Txn` contract's `If` (`Txn.IfTriple`). -/
def txn.If.spec : Prop :=
  ∀ (t : Loc) (γ : Cluster) (who : Principal) (ctx : GoInterface),
  Txn.IfTriple (GF := GF) (t @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty @!! go!"If")
    (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.txn.ty) #t) γ who ctx

end spec

end ClientV3
end EtcdGrove
end Perennial
