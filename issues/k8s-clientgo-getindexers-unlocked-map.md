---
upstream: none
checked: 2026-11-01
links: []
blocks-proof: no
---

# client-go: `Indexer.GetIndexers` races with `AddIndexers` (concurrent map read and write)

`GetIndexers` on a client-go `Indexer` (a shared informer's store, or `cache.NewIndexer`) returns
the store's own indexers map, read without the store's lock, while `AddIndexers` writes that map
under the lock. A caller reading the result (`GetIndexers()[name]`, as `pkg/controller`'s
`AddPodNodeNameIndexer` does) while another goroutine adds indexers is a concurrent map read and
write: the race detector reports it, and Go may abort the process (`fatal error: concurrent map
read and map write`).

**Expected:** `GetIndexers` should be safe to call concurrently with the store's other methods, as
the store is documented to be
([`ThreadSafeStore`](https://github.com/kubernetes/kubernetes/blob/v1.37.2/staging/src/k8s.io/client-go/tools/cache/thread_safe_store.go#L31-L34):
"allows concurrent indexed access"), including `AddIndexers`, which "supports adding indexes after
the store already has items" ([`Indexer`](https://github.com/kubernetes/kubernetes/blob/v1.37.2/staging/src/k8s.io/client-go/tools/cache/index.go#L50-L54));
`SharedIndexInformer.AddIndexers` refuses only a stopped informer, not a started one.

**Impact:** programs that add indexers to a running shared informer while another component of
the same process reads its indexers: `pkg/controller`'s `AddPodNodeNameIndexer` and
`AddPodControllerIndexer` (which check `GetIndexers()` before adding), and the mutation cache's
`ByIndex` (`mutation_cache.go`, on every call). kube-controller-manager does not reach it: it
builds all controllers, and so adds all their indexers, sequentially before starting the
informers. Out-of-tree controllers that register indexers lazily, after start, can.

**Reproduction:** `TestGetIndexersRacesAddIndexers` in
[`issues/k8s-clientgo-getindexers-unlocked-map/getindexers_race_test.go`](k8s-clientgo-getindexers-unlocked-map/getindexers_race_test.go),
copied into `tools/cache` of a writable copy of `k8s.io/client-go@v0.37.2` (Kubernetes v1.37.2, the
latest release, 2026-11-01), go1.27.3 linux/amd64:

```
$ GOWORK=off GOFLAGS=-mod=mod go test -race ./tools/cache -run TestGetIndexersRacesAddIndexers -count=1
==================
WARNING: DATA RACE
Read at 0x00c00032a000 by goroutine 11:
  runtime.mapaccess2_faststr()
  runtime.mapaccess1_faststr()

Previous write at 0x00c00032a000 by goroutine 10:
  runtime.mapassign_faststr()
  k8s.io/client-go/tools/cache.(*storeIndex).addIndexers()
      tools/cache/thread_safe_store.go:164 +0x87e
  k8s.io/client-go/tools/cache.(*threadSafeMap).AddIndexers()
      tools/cache/thread_safe_store.go:506 +0xe4
  k8s.io/client-go/tools/cache.(*cache).AddIndexers()
      tools/cache/store.go:346 +0x47
```

**Cause:** [`threadSafeMap.GetIndexers`](https://github.com/kubernetes/kubernetes/blob/v1.37.2/staging/src/k8s.io/client-go/tools/cache/thread_safe_store.go#L498-L500)
returns `c.index.indexers` without taking `c.lock`, and hands out the map itself;
[`storeIndex.addIndexers`](https://github.com/kubernetes/kubernetes/blob/v1.37.2/staging/src/k8s.io/client-go/tools/cache/thread_safe_store.go#L155-L167)
writes the same map under the write lock.

## Proof

no: `threadSafeMap.GetIndexers`'s spec (`Spec/k8s_io/client_go/tools/cache/threadSafeMap__GetIndexers.lean`)
gives only the map's location, whose contents the store lock guards; the DaemonSet controller's
`AddPod*Indexer` reads need no concurrent `AddIndexers`, which kube-controller-manager meets (all
indexers added before the informers start).

## Fix

In `GetIndexers`, take `c.lock.RLock()` and return `maps.Clone(c.index.indexers)`.
