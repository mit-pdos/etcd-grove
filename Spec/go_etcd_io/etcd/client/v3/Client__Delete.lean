/-
`(*clientv3.Client).Delete`: the `KV` method promoted through `Client`'s embedded `KV` field.

Users: `client/v3/concurrency` (`mutex.go:118` `Unlock`'s `Delete` of the key, `election.go:124`
`Resign` via `Txn`), `experimental/recipes` (`double_barrier.go`, `rwmutex.go` `Unlock`),
leasing (`leasing/kv.go` `Delete` through `Do`), the examples (`txnlin/linkvtxn.go:885`
`callDel`). Most users call it on the client; snippets: `clientv3kv/put_get.go` (`ReqDeleteThenGet`).

Proof sketch: `isClient_KV`: the field `c.KV` holds `v` with `kvAt v γ who`, read-only; the promoted
method loads it and calls `v.Delete` (Go's method set of `*Client`); `kvAt_methods`' `Delete` at `v`.

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

/-- `c.Delete(...)` on a client (`isClient`): the method of its `KV` field, promoted (`Client` embeds
`KV`): the KV contract's `Delete` (`KV.DeleteTriple`). -/
def Client.Delete.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal),
  KV.DeleteTriple (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"Delete")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isClient c γ who)) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
