---
upstream: none
checked: 2026-10-26
links: []
---

# The watch cache keeps an object whose update failed in the indexer

- **Status**: a bug (a wrong result), on an error path: an index function that returns an error.
  The watch cache's own index functions (registry code, e.g. pods by `spec.nodeName`) fail only on
  an object of the wrong type, so it is unlikely in practice; but nothing states that index
  functions must not fail, and the code handles the error as if the update were undone.
- **Where**: `k8s.io/apiserver@v0.0.0-20261021221356-9c4ec15b8038` (kubernetes master of
  2026-10-21, the pin of `examples/k8setcd3/go.mod`), `pkg/storage/cacher/store`:
  - `watch_cache_storage.go:165`, `WatchCacheStorage.UpdateStore`: it applies the update to the
    B-tree (`w.store.addOrUpdateElem` / `deleteElem`), then to the indexer
    (`w.indexer.updateElem`), and on the indexer's error returns `nil, err` without publishing a
    snapshot; the B-tree keeps the update.
  - `indexer.go:72`, `indexer.updateElem`: returns on the first index function's error, after
    updating the indexes it iterated over before (map order).
  - `watch_cache.go:213`, `watchCache.processEvent`: on `UpdateStore`'s error returns before
    `w.history.updateCache` and the `resourceVersion` update: the event is not in the history.
  - client-go `tools/cache/reflector.go:1039-1075`: the reflector only logs the store's error and
    goes on; once past the initial list it calls the watch cache's `UpdateResourceVersion` with
    the event's revision (`reflector.go:632`), which publishes `w.store.Clone()`
    (`watch_cache_storage.go:190`).
- **What happens**: after an Add/Update/Delete whose index function fails, the store's B-tree has
  the update, the history does not, and some indexes may have it. The next published snapshot
  (the next event's, or the bookmark-like `UpdateResourceVersion` the reflector issues right
  away) contains it: a GET or LIST from the cache returns the object (or misses a deleted one),
  while a watch from an earlier revision never delivers its event, and lists by index disagree
  with lists without. Reproduction: `k8s-watchcache-index-error-partial-update/index_error_test.go`
  (package `store`); in a writable copy of the module,
  `GOWORK=off GOFLAGS=-mod=mod go test ./pkg/storage/cacher/store/ -run TestUpdateStoreIndexErrorLeavesElement -v`
  logs that the snapshot at revision 12 contains `/bad`, whose update at 11 failed, and that the
  index has no entry for it (2026-10-26).
- **Expected**: an update that `UpdateStore` reports as failed has no effect on what the cache
  serves; or the failure stops the cache (re-list) instead of being logged and skipped.
- **How the proof handles it**: the store's specs (KEP-6404 work, `notes/kep-6404-plan.md`) take
  index functions that do not fail as a premise (to be stated with the store's specs).
- **Possible fixes**: compute the index values before touching the B-tree (the index functions
  only read the objects), and fail before any mutation; or undo the B-tree's update on the
  indexer's error; or treat the error as fatal for the cache (re-initialize it).
- **Found**: 2026-10-26, reading `cacher/store` to specify it for KEP-6404.
