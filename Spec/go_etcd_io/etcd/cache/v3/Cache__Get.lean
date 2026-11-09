/-
`(*Cache).Get(ctx, key, opts...)` (`cache/cache.go`): a read served from the cache's snapshots.

Users (patterns):
* a read at a revision the caller has watched up to, checked against the watch's events:
  `examples/etcd/cache/cachekv.go` (`c.Get(gctx, prefix, WithPrefix(), WithRev(r))`, `checkGet`);
  snippet `cache/get.go` `ReqGetAgreesWithWatch`;
* a linearizable read after an acknowledged write (etcd's `tests/integration/cache_test.go`
  `testGet`/`testWithPrefixGet`: the cache as a drop-in `Getter`, compared with the client's `Get`);
  snippet `ReqGetAfterPut`;
* a serializable read after `WaitForRevision(rev)` (`testGet`: `WaitForRevision(ctx, followupRev)`,
  then `Get(..., WithSerializable())`); snippet `ReqWaitThenSerializable`;
* the range checks (`TestCacheWithPrefixGetOutOfScope`: `errors.Is(err, ErrKeyRangeInvalid)`;
  `TestCacheUnsupportedGetOptions`: `ErrUnsupportedRequest`); snippet `ReqRangeInvalid`.

Proof sketch: `store.LatestRev.spec` (`storeRevLb`); if `0`, `Cache.WaitReady.spec`. `OpGet.spec`
(W0; `¬ prefixAndFromKey gs`) gives `opAt op (opGetM key gs)`; `Cache.validateGet.spec`
(`getUnsupported`, `rangeOk` on `cacheRange key o`: the error arm, `ErrKeyRangeInvalid`'s value from
`init.spec`). The `Op`'s getters (`RangeBytes`, `Rev`, `IsSerializable`: W0's `Op__*` specs). If not
serializable: `Cache.serverRevision.spec` gives `etcdLb γ σ1` with `serverRev = σ1.kv.rev` and
`Reach σ0 σ1` (`etcdLb_ord` against the caller's `σ0`, which the cluster passed before the call: the
client's update fires after it); `requestedRev > serverRev` is `ErrFutureRev`
(`errVal .futureRev`, an error arm); `Cache.waitTillRevision.spec` gives `storeRevLb s serverRev` or an
error. Then `store.Get.spec` at `startKey = key`, `endKey = o.rangeEnd`, `rev = o.rev`: the snapshot
newest at or below the revision asked for, whose content is `σ.kv.storeAt` of that revision under
the prefix (the store's certificate: each snapshot is etcd's state under the prefix at its revision,
and the gap after it quiet, `Internal.lean`'s `isStore`), restricted to the range (`snapshot.Range.spec`;
`rangeOk` puts the range inside the prefix), and the latest revision `L ≥ serverRev ≥ σ0.kv.rev`
(and `≥ r0`, `storeRevLb` monotone). The response is a fresh `RangeResponse` whose key-values are the
snapshot's (read-only), `rangeRespOwn ... DFrac.discard`.

Changes: (round 1) a thread token, given back, for the store's and the progress requestor's reader
slots (the read locks of `LatestRev`, `waitTillRevision`, `getSnapshot`: a thread pool over
Perennial's `RWMutex`, as leasing's reads); `ErrUnsupportedRequest` stated (`wrapsErr`). From
`specs-ref`'s `Cache__Get.lean`: stated over W0's model (`Store.rangeKVs` of
`σ.kv.storeAt`, `etcdLb`) instead of the old `isEtcdKvs`/`EtcdModel` class; the old reader token
(`cacheReader`, given back) replaced by the thread token (the snapshots are frozen, `ownBTree_persist`, and
read outside the lock; the lock's reader slots are what the token pays for); the old `storeRevLb` premise is the
client-facing `cacheRevLb c r0`; the linearizable freshness is anchored at a state the caller passes
(`etcdLb γ σ0`), as 1f's waiting calls do; the context must carry the cache client's principal (`ctxPrin ctx who`, W0's premise of the client's `Get`, to which the cache passes it); the error arms are not classified beyond what callers test
(the range check, by value).

Margin: the code's errors are, besides the range check, the context's, the client's (any `Get`
error, including definite ones), `ErrFutureRev` (a revision above the cluster's or the cache's),
`ErrCacheTimeout` (the cache did not catch up within `WaitTimeout`), `ErrCompacted` (a revision below
the cache's history window), `ErrNotReady`, a negative revision's, and the wrapped
`ErrUnsupportedRequest`: all `err ≠ nil` here. A keys-only request is answered with values (the
cache ignores `WithKeysOnly`: a deviation from the client's `Get`, reported in batch-1g.md).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cache

open Iris Iris.BI EtcdModel EtcdWire ClientV3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **`c.Get(ctx, key, opts...)`**: for the request `o = OpGet(key, opts...)` on the range
`cacheRange key o`, either no response and an error (`getErr`: `ErrKeyRangeInvalid` for a range the
cache does not serve), or (the request served, `rangeOk`) the response `getOk`: the cache's latest
revision `L` as the header's, and the key-values of etcd's store at the revision asked for (`L` for
`0`) in the range, at a state the cluster reached; at least as fresh as `σ0` (a state the caller knew
at the call) unless serializable, and at least `r0` (a revision the caller knew the cache reached). -/
def Cache.Get.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (pfx : GoString) (ctx : GoInterface) (key : GoString) (opts : GoSlice)
    (gs : List (OpM → OpM)) (σ0 : State) (r0 : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isCache c γ who pfx ∗ Context.ctxOk ctx ∗ ctxPrin ctx who ∗
      optsAt opts gs ∗ ⌜¬ prefixAndFromKey gs⌝ ∗ etcdLb γ σ0 ∗ cacheRevLb c r0 ∗ threadTok }}
    (App (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.Cache.ty @!! go!"Get")) (Val #ctx)) (Val #key)) (Val #opts))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); optsAt opts gs ∗ threadTok ∗
      (getErr pfx ctx (cacheRange key (opGetM key gs)) (opGetM key gs) resp err ∨
       (⌜¬ getUnsupported (opGetM key gs) ∧ rangeOk pfx (cacheRange key (opGetM key gs))⌝ ∗
        getOk c γ (cacheRange key (opGetM key gs)) (opGetM key gs) σ0 r0 resp err)) }}

end spec

end Cache
end EtcdGrove
end Perennial
