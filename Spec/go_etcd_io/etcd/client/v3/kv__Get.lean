/-
`(*clientv3.kv).Get` (`client/v3/kv.go`).

Users: `client/v3/concurrency` (`mutex.go:73` `Get` of the lock key, `election.go:165` `Leader`,
`key.go:44` `waitDeletes`' `Get` with `WithLastCreate()`/`WithMaxCreateRev`, `stm.go:262`
`fetch` with `WithSerializable` for `stmSerializable`), `experimental/recipes` (`client.go`,
`queue.go:53` `WithFirstKey()`, `rwmutex.go` `WithLastRev()`/`WithMaxModRev`), the cache
(`cache/cache.go` `Get` with `WithPrefix`, `WithRev`, `WithCountOnly`, `WithLimit`), Kubernetes'
store (`etcd3/store.go` `Get` with `WithRange`, `WithLimit`, `WithRev`, `WithKeysOnly`), the
examples (`txnlin/linkvtxn.go:837` `callGet`, `:863` `callList` with `WithRange`). Snippets:
`clientv3kv/put_get.go`, `clientv3kv/history.go` (`ReqGetAtRevision`), `clientv3kv/ops.go`
(`ReqSerializableGet`, `ReqGetOptions`).

Proof sketch: `OpGet.spec` (premise `¬ prefixAndFromKey gs`), then `kv.Do.spec` with `.range
(opGetM key gs).rangeReq`, a read: the caller's persistent update passes as is; `doReply`'s
range case is `getReply`; `ContextError.spec` as in `kv.Put`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/kv__Get.lean`: as `kv.Put`'s; in addition a
serializable get is the same spec (the model's range step answers it at a member's view), and
keys-only, count-only, sorted, limited and filtered gets are all covered (the old get model held
only for gets that are not keys-only: `issues/etcd-range-keys-only-lease.md` is now in the model).

Margin: a serializable get is answered at some member's view with no lower bound (it may be
older than the caller's own last write): the model says exactly that.
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

/-- `kv.Get` meets the KV contract's `Get` (`KV.GetTriple`, `Api.lean`), for a `*kv` of the
cluster `γ` as `who` (`kvHandle`). -/
def kv.Get.spec : Prop :=
  ∀ (kv c : Loc) (γ : Cluster) (who : Principal),
  KV.GetTriple (kv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.kv.ty @!! go!"Get")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ kvHandle kv c γ who ∗ clientReady c)) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
