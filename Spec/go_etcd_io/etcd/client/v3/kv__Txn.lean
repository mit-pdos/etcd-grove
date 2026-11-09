/-
`(*clientv3.kv).Txn` (`client/v3/kv.go`).

Users: `client/v3/concurrency` (`mutex.go:83` `tryAcquire`, `election.go:69` `Campaign`, `stm.go:203`
`commit`), `experimental/recipes` (`key.go:91` `putNewKV`, `queue.go`), leasing (`leasing/txn.go`),
Kubernetes' store (`etcd3/store.go` `Create`/`GuaranteedUpdate`/`Delete`: `If(ModRevision(key) =
rv).Then(OpPut(...)).Else(OpGet(key))`) and compactor (`etcd3/compact.go`: `If(Version(key) =
t).Then(OpPut(key, "")).Else(OpGet(key))`), the examples (`txnlin/linkvtxn.go:935` `callTxn`).
Snippets: `clientv3kv/txn.go`.

Proof sketch: allocates `&txn{kv, ctx, callOpts}` with a fresh mutex: `txnAt` of the concrete `*txn` is its
fields under its mutex's lock invariant (`sync.Mutex`, Perennial) with `TxnSt.empty`, the kv's
handle and the context (`ctxOk`).

Changes: none (no old spec): added (`Txn(ctx)` was inlined in the users' proofs).

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

/-- `kv.Txn` meets the KV contract's `Txn` (`KV.TxnTriple`, `Api.lean`), for a `*kv` of the
cluster `γ` as `who` (`kvHandle`). -/
def kv.Txn.spec : Prop :=
  ∀ (kv c : Loc) (γ : Cluster) (who : Principal),
  KV.TxnTriple (kv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!! go!"Txn")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvHandle kv c γ who ∗ clientReady c)) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
