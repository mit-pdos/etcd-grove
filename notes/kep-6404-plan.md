# Plan: KEP-6404 (API server write throughput) — GETs served from the watch cache

Status: started 2026-10-26 (branch `kep-6404`); "Progress" below. The user asked (2026-10-26) to start "proving code related
to" [KEP-6404](https://github.com/kubernetes/enhancements/blob/master/keps/sig-api-machinery/6404-apiserver-write-throughput/README.md)
after watchkv's move off the adapter, autonomously; the message was cut off after "Our goal is
to." The goal below is this note's reading of it, to be confirmed.

## What the KEP changes

Allocation, not etcd, limits kube-apiserver's write throughput; the KEP's main design is to
**serve every GET from the watch cache** (feature gate `ConsistentGetFromCache`, kube-apiserver
only), including:

- consistent GETs (`resourceVersion=""`): `cacher.Get` learns the revision it must reach (etcd's
  current revision, `getCurrentRV`, or the latest known) and reads
  `watchCache.WaitUntilFreshAndGet(ctx, requiredRV, key)` from the cache's B-tree snapshot;
- `GuaranteedUpdate`'s re-read after a failed optimistic transaction (a `ModRevision` conflict):
  instead of a GET to etcd, wait until the watch cache reaches the revision of the failed
  `TxnResponse` and read the already-decoded object from it.

It claims "the API semantics and consistency guarantees remain identical". At the pinned apiserver
(`k8s.io/apiserver@v0.0.0-20261021221356-9c4ec15b8038`) the gate is not implemented; the code it
builds on is (`pkg/storage/cacher`: `watch_cache.go`'s `waitUntilFreshLocked`,
`waitAndGetLatestSnapshot`, `WaitUntilFreshAndGet`, `checkSnapshotResourceVersion`; `store/`, the
snapshotted B-tree, KEP-4988; the delegator's consistent reads from cache, KEP-2340). Upstream
tracking: kubernetes#142223, kubernetes#142228 (open, no implementing PR as of 2026-10-26).

## The goal (this note's reading)

Prove the KEP's claim at the code: a GET served from the watch cache is a **linearizable read of
the store** (the etcd3 store's `correctness.Model`, `notes/k8s-etcd3-plan.md`), and the conflict
re-read gives `GuaranteedUpdate` a state at least as new as the one it lost to, so the store's
generic specs (phase 4 of the etcd3 plan) still hold with the cache in the loop. Concretely:

1. **The watch cache's state is etcd's at its revision.** `processEvent` applies the reflector's
   events in revision order; each snapshot `store.Snapshot` at revision `r` is the store's state
   at `r` (the etcd KV state `σ.at r` of the client's Watch spec, D47, restricted to the
   resource's prefix and decoded). This rests on the client's Watch spec (repeated reads of the
   KV state) through the reflector, the cacher's `ListerWatcher` (`lister_watcher.go`) over the
   etcd3 store's watcher.
2. **`waitUntilFreshLocked(rv)`** returns only when the cache's `resourceVersion ≥ rv` (or an error
   on timeout/cancel); `WaitUntilFreshAndGet` with `getCurrentRV` therefore reads a snapshot at
   a revision at least etcd's current one at the call, so the read linearizes in the call's
   interval. (Not through the KV's read update `kvReadAu` fired inside `getCurrentRV`: the GET's
   spec takes `getCurrentRV`'s behaviour as a persistent premise, `wcGetOk`, whose fact `curRV` is
   then persistent too. Instead the caller rebuilds `wcGetOk` for each call with `curRV n :=
   ⌜r0 ≤ n⌝`, `r0` a persistent lower bound of etcd's revision taken at the call's start, from a
   `getCurrentRV` spec "given the bound `r`, returns `n ≥ r`"; then `r0 ≤ m ≤ st.2`, `Ψ` puts
   `st.2` at or below etcd's revision at the return, and the read linearizes at the moment the
   revision is `st.2`, which rises by one per transaction. Found by the spec's review.)
3. **No reachable panic**: `checkSnapshotResourceVersion`'s panic (`PanicOnCacheInconsistency`)
   is unreachable (the snapshot's revision is the cache's under the lock), and the B-tree
   snapshots' code is the verified k8s fork (`Proof/k8s_io/utils/third_party/forked/golang/btree/`).
4. **The conflict path** (once implemented upstream, or as a fork branch implementing the KEP's
   design): after a failed `OptimisticPut` at the response's revision `r`, waiting for the cache
   to reach `r` and reading the key gives the object's state at some revision `≥ r`, which is
   what `GuaranteedUpdate`'s retry needs (the etcd3 store's D30l read-or-write update).

## Steps

1. Translate `k8s.io/apiserver/pkg/storage/cacher` (its `store` subpackage with bodies first,
   then `watch_cache.go`; `cacher.go`, the delegator and the reflector names-only at first) as a
   project of `etc/goose.py` next to `k8s-apiserver`; record what Goose cannot translate
   (`iter.Seq2` ranges, generics, `sync.Cond` with timers) in `notes/perennial-changes.md`.
2. Specs and proofs of `store/` over the B-tree's `ownBTree` (snapshots are immutable clones).
3. `watchCache`'s invariant: its lock, `resourceVersion`, the snapshot history, `cond`; specs of
   `processEvent`, `UpdateResourceVersion`, `waitUntilFreshLocked`, `WaitUntilFreshAndGet`.
4. Tie the cache's state to the KV state through the client's Watch spec (no adapter, no members,
   as watchkv since 2026-10-26).
5. The KEP's conflict path, on a fork branch if upstream has not implemented it yet.

## Progress (2026-10-26, branch `kep-6404`)

- **Translation** (project `k8s-apiserver` of `etc/goose.py`): `cacher/store` with bodies; the
  cacher (`Code/k8s_io/apiserver/pkg/storage/cacher.toml`) with `watch_cache.go`'s `watchCache`
  methods' bodies, the rest names-only; `cacher/progress`'s `Add`/`Remove`; names-only
  `consistency`, `key`, `delegator`, `metrics`, client-go's `tools/cache` (its indexer types
  translated), `util/consistencydetector`, `util/watchlist`, component-base's `metrics`; `watch`'s
  event-type constants. Goose gaps hit: G3 (a type of a package the file does not import: the
  cacher's metrics; worked around, at the cost of `watchCacheEvent` being axiomatized, so
  `processEvent` and `watchCache.UpdateResourceVersion` cannot be proved until G3's general fix)
  and a constraint interface's `comparable` (`notes/perennial-changes.md`).
- **A bug** (`issues/k8s-watchcache-index-error-partial-update.md`, reproduced): an index function's
  error leaves the update in the store's B-tree, and the next snapshot serves it, without the
  event in the history.
- **The store** (`Proof/k8s_io/apiserver/pkg/storage/cacher/store/`; `Defs.lean`, `DefsWCS.lean`;
  specs reviewed by a fresh subagent, its findings applied): `btreeStore`'s `newBtreeStore`,
  `Clone`, `ResourceVersion`, `getByKey`, `GetByKey`, `addOrUpdateElem`, `deleteElem` proved over
  the verified B-tree; `snapshotter.Add`/`UpdateResourceVersion` proved (their panics unreachable);
  `WatchCacheStorage.LatestSnapshot` (the lock-free read: the caller's view shift at the atomic
  load, against the published state; `isWCS`'s caller fact `Ψ` of every published state),
  `UpdateStore` and `UpdateResourceVersion` (the publication at the atomic store, the ghost state
  split between the invariant, the lock and the writer, `wcs_update`) proved.
  `indexer.updateElem` proved over `indexer.add`/`delete` (the map range over the index
  functions, the nested maps through `ownIdx`; its spec keeps only the indexer's ownership: no
  read through an index is verified); `btreeStore.Replace`'s proof, `Replace`,
  `NewWatchCacheStorage` and the read-locked methods (they need reader tokens) are left.
- **The progress requester**'s `Add`/`Remove` proved (`isPR`).
- **The watch cache's reads** (`Proof/k8s_io/apiserver/pkg/storage/cacher/`, `DefsWC.lean`; linked
  in its `Link.lean`, `etc/gen-link.py --cacher`): `checkSnapshotResourceVersion`,
  `getLatestSnapshotLocked`, `waitUntilFreshLocked`, `waitAndGetLatestSnapshot` and
  `WaitUntilFreshAndGet` proved. The lock's resource is `∃ st, resourceVersion ↦{q} st.2 ∗ wcsOwn
  γ q st`: a reader under the read lock holds part of the writer's token, so the snapshot it loads
  is the cache's state at `w.resourceVersion`, and `checkSnapshotResourceVersion`'s panic is
  unreachable. The wait is on the condition variable over the read lock (`sync.Cond.wp_Wait_with`
  with `rlocker_isLockerWith`), with the timeout goroutine, the read-wait histogram and the
  progress requester. **The cached GET** (`WaitUntilFreshAndGet`): its version is the
  versioner's parse of `resourceVersion` or, for `""`, `getCurrentRV`'s with the caller's fact
  `curRV` (`wcGetOk`); without an error, the value and existence of the key in a state `st` the
  store published (with `□ Ψ st`), at that version or later, and `rv = st.2`. The callees' trust
  specs: the config's clock (`clockOk`), component-base's `HistogramVec.WithContext` (axiom), the
  cacher metrics' package fact (`WatchCacheReadWait`'s labels, axiom),
  `tracing.SpanFromContext` (axiom), `storage.NewTooLargeResourceVersionError` (proof `sorry`: it
  needs `apierrors.NewTimeoutError`).
- **The current revision** (step 2): `store.GetCurrentResourceVersion` (the etcd3 store's, the
  cacher's `getCurrentRV`) proved, linked in the etcd3 store's Link: a linearizable read through
  the client's `Get` with the caller's read updates as `store.Get`'s, returning the revision of
  the state they fired at (not `0`). `wcGetOk` takes its context's precondition (`ctxPre`: the
  store's `ctxOk`/`ctxErrClient`), which `WaitUntilFreshAndGet` takes for its own context. Left:
  `wcGetOk`'s `getCurrentRV` premise from this spec, for the function the cacher stores (the
  method value `config.Storage.GetCurrentResourceVersion`, `NewCacherFromConfig`, not translated
  yet), with `Q` the lower bound of etcd's revision at the call's start.
- **Next**: tie `Ψ` to etcd's state (a published state at revision `r` is etcd's KV state at `r`:
  the reflector's list and watch over the KV/Watch specs, `processEvent`, blocked on G3) and
  `curRV` to the read's linearization (per call, `curRV n := ⌜r0 ≤ n⌝` for a lower bound `r0` of
  etcd's revision at the GET's start, step 2: the cacher's `getCurrentRV`, a quorum `Get` over
  the client specs, specified as "given the bound `r`, returns `n ≥ r`"); then `Cacher.Get` over
  `WaitUntilFreshAndGet`, and the KEP's `GuaranteedUpdate` re-read from the cache.
