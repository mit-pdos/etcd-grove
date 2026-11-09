/-
`(*clientv3.retryKVClient).Txn` (`client/v3/retry.go`).

Users: `kv.Do`, `kv.Compact`, `txn.Commit` (through `kvHandle`'s `remoteKVAt`).

Proof sketch: the stub's `Txn` with the same options (`retryKVHandle`'s `remoteKVAt`): the retry interceptor's default policy, not repeatable, resends only a request never sent (`isSafeRetryMutableRPC`), so the exclusive update passes.

Integration (I1): the stub's call is 3h's generated `KVClient` method, i.e. `cc.Invoke` through the
client's unary interceptor: 1c's `uiOk_call` (with `clientReady c`, from `retryKVHandle rkv c`'s premise)
over 2a's `AttemptTriple` realization (`Grpc.attemptOk_call`, `V3rpc.etcdUnary`), its outcomes mapped to
`wireReply`/`wireIndef` by `Rpctypes.callErr_view` (a definite answer whose error rpctypes does not map,
e.g. `invalidClientAPIVersion`, reaches the client as `.other`: the update fired, `Q` dropped, the
`wireIndef` disjunct). **Open**: this call's update is over `Step p rq σ σ' res lo` (`authLb γ lo`), 1c's `callAU`
now takes `lo` (`AttemptTriple`, `uiOk_call` bind it with `authLb γ lo`), while 2a's `etcdUnary` carries
none (its update is over `Step p rq` at the default `lo = 0`, which a client's `lo`-update does not
accept): it must carry `lo` and `authLb γ lo` (`notes/specs-only/integration-I1.md`).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/retryKVClient__Txn.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

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

/-- `rkv.Txn` meets the wire-level contract's `Txn` (`RemoteKV.TxnTriple`). -/
def retryKVClient.Txn.spec : Prop :=
  ∀ (rkv c : Loc) (γ : Cluster) (who : Principal),
  RemoteKV.TxnTriple (rkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.retryKVClient.ty @!! go!"Txn")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryKVHandle rkv c γ who ∗ clientReady c)) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
