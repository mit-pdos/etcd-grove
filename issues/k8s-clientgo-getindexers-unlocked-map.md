---
upstream: unchecked
checked: 2026-10-27
links: []
---

# client-go's `GetIndexers` returns the store's indexers' map, read and written under different rules

- **Status**: a data race (an unstated precondition of `GetIndexers`). `threadSafeMap.GetIndexers`
  returns the store's own `Indexers` map, reading the field without the store's lock, and the
  caller then reads the map (`GetIndexers()[name]`); `AddIndexers` writes the same map under the
  store's write lock (`storeIndex.addIndexers`: `i.indexers[k] = v`). A `GetIndexers()` read
  concurrent with an `AddIndexers` is a concurrent map read and write (Go may abort the process:
  `fatal error: concurrent map read and map write`). Since `sharedIndexInformer.AddIndexers` no
  longer refuses a started informer (it checks only `stopped`, `shared_informer.go:983`), the two
  can run concurrently on a shared informer: two controllers sharing the pod informer each run
  `pkg/controller`'s `AddPodNodeNameIndexer`/`AddPodControllerIndexer`, whose first step is the
  unlocked `podInformer.GetIndexer().GetIndexers()[...]`, and the mutation cache's `ByIndex`
  (`mutation_cache.go:235`) reads it on every call. Nothing in the API says the returned map must
  not be read while indexers may be added, nor that it is the store's own map rather than a copy.
- **Where**: `k8s.io/client-go/tools/cache/thread_safe_store.go` at the pinned
  `v0.0.0-20261021054439-569675c57fa3`: `GetIndexers` (line 501, `return c.index.indexers`, no
  lock), `AddIndexers` (505, under `c.lock.Lock()`) and `storeIndex.addIndexers` (155-167);
  `store.go:317` (`cache.GetIndexers`), `index.go:50` (the interface's doc: "GetIndexers return the
  indexers").
- **What happens** (Go test against the pin, `go test -race`: `WARNING: DATA RACE`, write at
  `storeIndex.addIndexers` `thread_safe_store.go:164`, previous read at the caller's map access):

  ```go
  func TestGetIndexersRacesAddIndexers(t *testing.T) {
      idx := cache.NewIndexer(cache.MetaNamespaceKeyFunc, cache.Indexers{})
      var wg sync.WaitGroup
      wg.Add(2)
      go func() {
          defer wg.Done()
          for i := 0; i < 1000; i++ {
              _ = idx.AddIndexers(cache.Indexers{fmt.Sprintf("i%d", i):
                  func(obj interface{}) ([]string, error) { return nil, nil }})
          }
      }()
      go func() {
          defer wg.Done()
          for i := 0; i < 1000; i++ {
              _ = idx.GetIndexers()["i0"] // as AddPodNodeNameIndexer does
          }
      }()
      wg.Wait()
  }
  ```
- **Expected**: `GetIndexers` returns a copy taken under the read lock (or is documented as
  unsafe concurrently with `AddIndexers`).
- **How the proof handles it**: `threadSafeMap.GetIndexers.spec` and `cache.GetIndexers.spec`
  (`Spec/k8s_io/client_go/tools/cache/`) give only the map's location `γ.im`; the map's points-to
  is the store lock's resource (`tsP`, `TSDefs.lean`), so no client can read the result without
  the lock. The DaemonSet controller's `AddPod*Indexer` reads will need the store quiescent
  (phase 5: before the informers start, no `AddIndexers` runs concurrently).
- **Possible fixes**: in `GetIndexers`, `c.lock.RLock(); defer c.lock.RUnlock()` and return
  `maps.Clone(c.index.indexers)`.
- **Found**: 2026-10-27, specifying `GetIndexers` for the DaemonSet plan's phase 4
  (`notes/k8s-daemonset-plan.md`): the result is a location whose contents the lock guards.
