/-
`(*clientv3.Client).Put`: the `KV` method promoted through `Client`'s embedded `KV` field.

Users: `client/v3/concurrency` (`Session`'s keys are written in transactions; `election.go` `Proclaim`
via `Txn`), `experimental/recipes` (`double_barrier.go:53` `Put` of the barrier key, `queue.go`,
`key.go:91` `putNewKV` via `Txn`), the examples (`examples/etcd/txnlin/linkvtxn.go:874` `callPut`,
`putget`, `putget3`, `compacted`, `compactwatch/compactkv.go`), Kubernetes' compactor
(`k8s.io/apiserver/pkg/storage/etcd3/compact.go`, through `Txn`). Most users call it on the client; snippets:
`clientv3kv/put_get.go` (`ReqPutThenGet`, `ReqPutRevision`), `clientv3kv/errors.go` (`ReqPutErrors`).

Proof sketch: `isClient_KV`: the field `c.KV` holds `v` with `kvAt v γ who`, read-only; the promoted
method loads it and calls `v.Put` (Go's method set of `*Client`); `kvAt_methods`' `Put` at `v`.

Changes: none (no old spec): the users call the KV methods on the client; added so that their proofs need no dispatch lemma.

Margin: as the KV method.
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

/-- `c.Put(...)` on a client (`isClient`): the method of its `KV` field, promoted (`Client` embeds
`KV`): the KV contract's `Put` (`KV.PutTriple`). -/
def Client.Put.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal),
  KV.PutTriple (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"Put")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isClient c γ who)) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
