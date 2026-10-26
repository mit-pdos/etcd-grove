# Plan: KEP-6404 (API server write throughput) — GETs served from the watch cache

Status: noted 2026-10-26, not started. The user asked (2026-10-26) to start "proving code related
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
   interval (the KV's read update, `kvReadAu`, fired by `getCurrentRV`'s etcd read).
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
