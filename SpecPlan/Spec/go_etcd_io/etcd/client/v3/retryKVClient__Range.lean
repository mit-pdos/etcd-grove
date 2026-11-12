/-
`(*clientv3.retryKVClient).Range` (`client/v3/retry.go`).

Users: `kv.Do`, `kv.Compact`, `txn.Commit` (through `kvHandle`'s `remoteKVAt`).

Proof sketch: appends `withRepeatablePolicy()` (1c's spec: an option `callOptsOk` admits with `rep = true`) to the options (a fresh slice unless the capacity allows: `callOptsOk` covers both), then the stub's `Range` (`retryKVHandle`'s `remoteKVAt`): the read's update is persistent, so the retries the policy allows fire it again harmlessly.

Integration (I1): the stub's call is 3h's generated `KVClient` method, i.e. `cc.Invoke` through the
client's unary interceptor: 1c's `uiOk_call` (with `clientReady c`, from `retryKVHandle rkv c`'s premise)
over 2a's `AttemptTriple` realization (`Grpc.attemptOk_call`, `V3rpc.etcdUnary`), its outcomes mapped to
`wireReply`/`wireIndef` by `Rpctypes.callErr_view` (a definite answer whose error rpctypes does not map,
e.g. `invalidClientAPIVersion`, reaches the client as `.other`: the update fired, `Q` dropped, the
`wireIndef` disjunct). The call's `lo` (`authLb γ lo`) is carried end to end: 1c's `callAU`,
`AttemptTriple`, `uiOk_call` and 2a's `etcdAU … lo` (`authLb γ lo`).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/retryKVClient__Range.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.
verify-round: the stale "Open" paragraph on 2a's `lo` dropped (A1-provability F8: 2a carries it).

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

/-- `rkv.Range` meets the wire-level contract's `Range` (`RemoteKV.RangeTriple`). -/
def retryKVClient.Range.spec : Prop :=
  ∀ (rkv c : Loc) (γ : Cluster) (who : Principal),
  RemoteKV.RangeTriple (rkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.retryKVClient.ty @!! go!"Range")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryKVHandle rkv c γ who ∗ clientReady c)) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
