/-
`New(client, prefix, opts...)` (`cache/cache.go`): a cache of the keys under `prefix`, over a client.

Users: `examples/etcd/cache/cachekv.go` (`cache.New(cli, prefix)`, default options); etcd's
integration tests (`tests/integration/cache_test.go`: `New(client, "")`, `New(client, "/foo")`,
`WithHistoryWindowSize(32)`, `WithHistoryWindowSize(1)`, `WithProgressNotifyInterval(d)`,
`WithPerWatcherBufferSize`, `WithResyncInterval`); no Kubernetes caller in the pinned sources
(Kubernetes' watch cache is its own, `k8s.io/apiserver/pkg/storage/cacher`). Snippet:
`cache/lifecycle.go` (`ReqNewDefault`, `ReqNewOptions`, `ReqInvalidConfig`).

Proof sketch: `defaultConfig.spec`, then each option's `cfgOptAt` triple on `&cfg` (the slice read-only,
`cfgOptsAt`), giving `cfg = cfgApply gs defaultConfigM`; `newCache.spec` with `realClock{}`
(`realClock.NewTimer.spec`, the `Clock` bundle `clockOk`). `newCache` checks `CfgValid` (the error
arm otherwise, `fmt.Errorf`); `context.WithCancel(Background())` (Perennial's `wp_WithCancel`, with
`isClosedchanInit`); the client's `Watcher` and `KV` fields from `isClient_fields`/`isClient_KV`
(1b's `watcherAt`, W0's `kvAt`); `newStore.spec`, `newReady.spec`,
`newConditionalProgressRequestor.spec` (over `watcherAt`'s `RequestProgress` triple), `NewDemux.spec`
(its resync loop on the wait group); allocates the cache's invariant (`isCache`: the store's,
demux's and ready's invariants, the read permission `etcdPeek γ`), the wait-group protocol and the
`cacheOpen` token; `Add(2)` and the two goroutines: `getWatchLoop.spec` with the loop token
(`cacheLoop`), `conditionalProgressRequestor.run.spec`. `CfgBounded` discharges the store's and
ring buffers' bounds and the watchers' `make(chan, n)`.

Changes: from `specs-ref`'s `New.lean`: over W0's client (`isClient c γ who`) instead of the old
`isEtcdClient` trust boundary (the client's contract is now W0's and 1b's specs); the cluster's read
permission `etcdPeek γ` replaces the old model class (the cache's own linearizable reads of the
cluster need an update to fire); the prefix-length bound (`≤ 2^28`, the old grpc message-size
scope) dropped (W0's client answers a too-large request with a refusal, an error the loop
retries); the thread bound (`ThreadBoundLe`) dropped (the wait group is backed by its goroutines'
thread tokens inside the proof, `notes/bounds-plan.md`); the result is the client-facing handle
`isCache` with `cacheOpen`, not the old `newCacheResult` bundle of internal handles.

Margin: the configuration's other fields (intervals, timeouts, buffer sizes) affect only liveness and
when a watcher is compacted, which no spec states.
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

/-- **`New(client, prefix, opts...)`**, for a client of the cluster `γ` (any principal), the
program's read permission over the cluster's state, and options with transformers `gs`: the
configuration is `defaultConfig()` with the options applied in order; if `newCache` rejects it
(`HistoryWindowSize ≤ 0` or `BTreeDegree < 2`), `nil` and an error; otherwise a cache of the keys
under `pfx` (`isCache`) with the whole `cacheOpen` token. An accepted configuration must be
`CfgBounded` (the code panics later otherwise). -/
def New.spec : Prop :=
  ∀ (client : Loc) (γ : Cluster) (who : Principal) (pfx : GoString) (sl : GoSlice)
    (gs : List (go_etcd_io.etcd.cache.v3.Config → go_etcd_io.etcd.cache.v3.Config)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ context.isClosedchanInit ∗
      isClient client γ who ∗ etcdPeek γ ∗ cfgOptsAt sl gs ∗
      ⌜CfgValid (cfgApply gs defaultConfigM) → CfgBounded (cfgApply gs defaultConfigM)⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.cache.v3.New)) (Val #client)) (Val #pfx)) (Val #sl))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
      ⌜¬ CfgValid (cfgApply gs defaultConfigM) ∧ c = null ∧ err ≠ GoInterface.nil⌝ ∨
      (⌜CfgValid (cfgApply gs defaultConfigM) ∧ err = GoInterface.nil⌝ ∗ isCache c γ who pfx ∗
        cacheOpen c 1) }}

end spec

end Cache
end EtcdGrove
end Perennial
