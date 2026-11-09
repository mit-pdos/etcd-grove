/-
`(*clientv3.watcher).Watch(ctx, key, opts...)` (`client/v3/watch.go`).

**Users** (pinned etcd `E = upamanyus/etcd/*@a4d2bb17`, Kubernetes apiserver `K`, `examples/` `X`;
every one through `Client.Watch` or a `Watcher` value, `watcherAt`), by pattern:
* wait for a delete from a known revision (`E client/v3/concurrency/key.go:30` `waitDelete`,
  `leasing/kv.go:210` `waitRescind`, `experimental/recipes/watch.go:28,38`): no gap from the start
  revision; snippet `clientv3watch/history.go` `ReqWatchWaitDelete`;
* resume after a `Get` at its revision + 1 and apply events as deltas (`naming/endpoints/
  endpoints_impl.go:131`, `mirror/syncer.go:119`, `server/.../v3discovery/discovery.go:370`,
  `leasing/kv.go:174`, `K etcd3/watcher.go:493`, `K etcd3/compact.go:269`, the cache
  `E cache/v3/cache.go:392`): revision order, no gap, no repeat, every event of a revision in one
  response; `history.go` `ReqWatchFromGet`, `ReqWatchRevisionWhole`;
* full-history checks (`X etcd/watch/watchkv.go:79`, `X etcd/partition/linkv3p.go:193`,
  `X etcd/auth/authkv.go:434,445`, `X etcd/compactwatch/compactkv.go:122`): events are the
  history's puts at their revisions; `history.go` `ReqWatchHistory`;
* progress notifications as bookmarks (`K etcd3/watcher.go`, the cache's `maxRev`):
  `progress.go`;
* compaction and errors end the watch (every user; `X compactwatch/compactkv.go:142` reads
  `CompactRevision`), a refused watch delivers nothing (`X etcd/auth/authkv.go:272`), `Created`
  first (`server/proxy/grpcproxy/leader.go:62`, the cache's readiness): `ending.go`;
* a watch from the current revision whose later writes must all appear (grpcproxy's coalescing,
  `server/proxy/grpcproxy/watch_broadcast.go:68`, `watcher.go:62-64`; `X k8s/compactor/
  compactor_test.go:104`): the floor; `history.go` `ReqWatchFromNow`; a watch chained from a
  bookmark (`K etcd3/store.go:1151` → `watcher.go:481`, the cache's `demux.go:137`):
  `ReqWatchChained`; the health probe (`grpcproxy/health.go:73`);
* `select` with the context, writing the response (`concurrency/election.go:190,223`,
  `namespace/watch.go:49`), Kubernetes' previous key-value (`K etcd3/event.go:67`):
  `consume.go`.

**Proof sketch.** `OpWatch.spec` (W0) gives the `Op` (`watchPanics` excluded); the filters are
built from it. `streamKeyFromCtx.spec` gives `ctxStreamKey ctx k`. The loop: `w.mu.Lock()` (the
watcher's lock invariant: `streams` is `nil` after `Close`, else a map from keys to `wgsAt` streams,
each key `k'` with the opening context's `ctxStreamKey ctx₀ k' ∗ ctxPrin who ctx₀ p₀` and the
stream at `p₀`); `nil` → a fresh channel, closed: `WatchPos.closed`. An existing stream of key `k`
is at the caller's principal `p` by `ctxStreamKey_prin` (verify-round W2). Else
`newWatcherGRPCStream.spec` for a missing key (with `clientReady c`, which turns the handle's
gated stub into `remoteWatchAt` for the stream's `run`, verify-round W3), then `select` on `reqc` (`wgsAt`'s protocol: the
`*watchRequest` goes with the `retc` protocol, whose receiver gets the channel `ch` with its
consumer: `watchChAt` at `WatchPos.init rev r0` with `etcdLb γ σ0`, `r0 = σ0.kv.rev`, the state of
the registration's `Created` response, whose header `H ≤ r0` the substream made its resume
revision before sending `ch` on `retc` (`wireStep`'s registration from `0` has floor `H`); or, for a
substream closed before it was registered, `WatchPos.closed`), `ctx.Done()` (W0's `Context.Done`,
`doneRecv`) or `donec` (closed: `closeErr` published; a closed channel with at most one error
response `Canceled` with `closeErr`: `WatchPos.closed`). Then `select` on `retc` or again
`ctx.Done()`/`donec`. Every channel is `make`'s (never `nil`). No thread token: the goroutines
`newWatcherGRPCStream` and `run` fork come with theirs (`wp_fork_tok`).

**Changes** from `specs-ref/.../watcher__Watch.lean`: the responses are persistent facts about the
history (`etcdLb` and `watchStep`), not firings of a persistent read update (D47); any range (from
`""` normalized as the member does, `OpM.watchReq`), any start revision (`0` and negative
included; was `≥ 1`), any context (`Context.ctxOk`; was `watchCtx`), filters, `prevKV`
(`WatchReq.prevOk`), fragments, `createdNotify`, progress; with auth (any mode, any number of
members): event responses carry the admitting auth state (`σa.permits who`), replacing the
one-member gate `watchCheckOk`; no size premise (`watchSizeOk`: an oversized create fails the
stream, `req/google_golang_org_grpc.md`), no `noDupKeys` server premise (a key written twice in
one revision gives both events, as the model's history has them).

verify-round (A2-provability W2, W3): the joined stream's principal from `ctxStreamKey_prin`; the
handle records its client `c` and the triple takes `clientReady c` (the stub opens streams through
the client's stream interceptor, whose token refresh reads `c.Auth`).

**Margin.** Liveness (that the channel closes when `ctx` is done or after an error, that a
`Created` or progress response comes) is not stated. A watch from the current revision is complete
from its first event, which is at most the floor + 1 (every event above the floor is delivered);
the code delivers nothing below `min(R + 1, H)` (`R` the member's registration revision, `H` the
creation's header), and may deliver revision `H`'s events, which precede the watch
(`issues/etcd-watch-current-resume-past-event.md`). The error responses' errors are classified
only by kind (`closeErrOk`). The admitting auth state `σa` is any state the cluster reached: a
lagging member checks its applied auth state, so a watch may be admitted after a revocation (an
up-to-date single member checks the current one; not stated).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiWatch

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

/-- `watcher.Watch` meets the `Watcher` contract's `Watch` (`Watcher.WatchTriple`, `ApiWatch.lean`),
for a `*watcher` of `γ` as `who` (`watcherHandle`) over a ready client (`clientReady c`). -/
def watcher.Watch.spec : Prop :=
  ∀ (w c : Loc) (γ : Cluster) (who : Principal),
  Watcher.WatchTriple (w @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.watcher.ty @!! go!"Watch")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ watcherHandle w c γ who ∗
      clientReady c)) γ who

end spec

end ClientV3
end EtcdGrove
end Perennial
