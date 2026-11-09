/-
`(*clientv3.Client).Get`: the `KV` method promoted through `Client`'s embedded `KV` field.

Users: `client/v3/concurrency` (`mutex.go:73` `Get` of the lock key, `election.go:165` `Leader`,
`key.go:44` `waitDeletes`' `Get` with `WithLastCreate()`/`WithMaxCreateRev`, `stm.go:262`
`fetch` with `WithSerializable` for `stmSerializable`), `experimental/recipes` (`client.go`,
`queue.go:53` `WithFirstKey()`, `rwmutex.go` `WithLastRev()`/`WithMaxModRev`), the cache
(`cache/cache.go` `Get` with `WithPrefix`, `WithRev`, `WithCountOnly`, `WithLimit`), Kubernetes'
store (`etcd3/store.go` `Get` with `WithRange`, `WithLimit`, `WithRev`, `WithKeysOnly`), the
examples (`txnlin/linkvtxn.go:837` `callGet`, `:863` `callList` with `WithRange`). Most users call it on the client; snippets:
`clientv3kv/put_get.go`, `clientv3kv/history.go` (`ReqGetAtRevision`), `clientv3kv/ops.go`
(`ReqSerializableGet`, `ReqGetOptions`).

Proof sketch: `isClient_KV`: the field `c.KV` holds `v` with `kvAt v γ who`, read-only; the promoted
method loads it and calls `v.Get` (Go's method set of `*Client`); `kvAt_methods`' `Get` at `v`.

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

/-- `c.Get(...)` on a client (`isClient`): the method of its `KV` field, promoted (`Client` embeds
`KV`): the KV contract's `Get` (`KV.GetTriple`). -/
def Client.Get.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal),
  KV.GetTriple (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"Get")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ isClient c γ who)) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
