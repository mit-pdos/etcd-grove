/-
`(*Cache).Watch(ctx, key, opts...)` (`cache/cache.go`): a watch served from the cache's history.

Users (patterns):
* a watch from a revision, read until a revision, checked against the writes (gap-free, exact):
  `examples/etcd/cache/cachekv.go` (`c.Watch(wctx, prefix, WithPrefix(), WithRev(2))`, `collect`);
  snippet `cache/watch.go` `ReqWatchFromRev`;
* a progress notification (`RequestProgress`, or `WithProgressNotify`'s timer) read and checked
  quiet: `cachekv.go` (`awaitProgress`, `checkProgress`); etcd's `TestCacheRequestProgress`,
  `TestCacheProgressNotify`; snippet `ReqProgressQuiet`;
* a watch "from now" and the end of a watch (the channel closed, or a compaction's cancel):
  `cachekv.go` (`WatchEnded`), etcd's `TestCacheLaggingWatcher` (`wantClosed`); snippet
  `ReqWatchEnds`;
* a rejected request (`TestCacheWatchUnsupportedOptions`, `TestCacheWithPrefixWatchOutOfScope`: one
  cancel response); snippet `ReqWatchRejected`.

Proof sketch: `Cache.WaitReady.spec`; on an error, a closed unbuffered channel (`closed`). `OpWatch.spec`
(W0), `Op.Rev`; `Cache.validateWatch.spec`: on a rejection a buffered channel holding the one cancel
response, closed (`rejected`). Otherwise `newWatcher.spec` (the configured buffer, `CfgBounded`; the
key predicate of `cacheRange`), `demux.Register.spec` at `o.rev`: the demux's invariant records the
watcher's position (`o.rev`, or "from now") and the consumer's ghost half; `Add(1)` with a fraction of
`cacheOpen` (the wait group's protocol: `Watch`'s `Add` never meets `Close`'s `Wait`); the goroutine
carries the watcher's consumer end (`watcherConsumer`), the response channel's producer end, and the
timer's (`realClock.NewTimer.spec`, `Timer` bundle): each response it forwards it received from the
watcher, whose responses the demux certified when it enqueued them (`watcher.enqueueResponse.spec`:
an events batch from the position, a progress notification quiet from it, a compaction's cancel),
so the forwarded response meets `cacheWatchAt_recv`'s arm; on `ctx`, the cache's context, or the
watcher's channel closed, it unregisters (`demux.Unregister.spec`) and closes the response channel
(`closed`). The consumer's position is the ghost half the demux's entry for the watcher shares.

Changes: from `specs-ref`'s `Cache__Watch.lean` and the delivery theorem (`cache_Watch_delivery`): the
log-level delivery theorem (a `cacheWatchLog` of all responses, `certChain` of `EtcdStep`s, `bs`
batches) is restated as a per-receive law (`cacheWatchAt_recv`) over the consumer's position, with
each response's fact `etcdLb γ σ ∗ ⌜deliv/quiet σ.kv ...⌝` in W0's model, which composes with every
other reply through the history; the old "slot" handles are the `cacheOpen` fraction.

Margin: a compaction's cancel carries `CompactRevision` (the demux's position for the watcher, at most
the consumer's) and `CancelReason = ErrCompacted.Error()`, not stated; the rejected response's
`CancelReason` is the rejection's error text. With `WithProgressNotify` the goroutine also sends a
progress notification every `ProgressNotifyInterval` when idle: a progress notification like any
other (the same arm).
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

/-- **`c.Watch(ctx, key, opts...)`**, by a holder of a fraction of `cacheOpen` (given back), for
the request `o = OpWatch(key, opts...)` (which must not panic) on the range `cacheRange key o`: the
response channel's consumer, at `watchStart` (a rejected request's one cancel response, or every
event under the range from `o.rev` on, or from the cache's newest revision for `0`), or already
closed (the context done before the cache was ready). -/
def Cache.Watch.spec : Prop :=
  ∀ (c : Loc) (γ : Cluster) (who : Principal) (pfx : GoString) (q : Qp) (ctx : GoInterface) (key : GoString)
    (opts : GoSlice) (gs : List (OpM → OpM)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ isCache c γ who pfx ∗ cacheOpen c q ∗
      Context.ctxOk ctx ∗ optsAt opts gs ∗ ⌜¬ (opWatchM key gs).watchPanics⌝ }}
    (App (App (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.cache.v3.Cache.ty @!! go!"Watch")) (Val #ctx)) (Val #key)) (Val #opts))
  {{ (ch : Loc), RET #ch; cacheOpen c q ∗ optsAt opts gs ∗
      (cacheWatchAt ch γ (cacheRange key (opWatchM key gs))
         (watchStart pfx (cacheRange key (opWatchM key gs)) (opWatchM key gs)) ∨
       cacheWatchAt ch γ (cacheRange key (opWatchM key gs)) .closed) }}

end spec

end Cache
end EtcdGrove
end Perennial
