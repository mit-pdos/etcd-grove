---
upstream: none
checked: 2026-10-26
links: []
blocks-proof: no
---

# The API server's watch cache keeps an object whose update failed in the indexer

`WatchCacheStorage.UpdateStore` (`apiserver/pkg/storage/cacher/store`, master of 2026-10-21) applies
an update to its B-tree and then to the indexer; when an index function returns an error it returns
the error, leaving the B-tree (and the indexes updated before the failing one) changed while
`watchCache.processEvent` drops the event from the history. The next published snapshot serves the
object to GET and LIST while a watch never delivers its event.

**Why not an issue:** a precondition kube-apiserver meets: the watch cache's index functions are
Kubernetes' own (registry code, e.g. pods by `spec.nodeName`), which fail only on an object of the
wrong type, which the cache never holds; the test reaches it only with an index function written to
fail.

## Proof

no: the store's specs take index functions that never fail as a premise
(`Spec/k8s_io/apiserver/pkg/storage/cacher/store/indexer__updateElem.lean`,
`Proof/k8s_io/apiserver/pkg/storage/cacher/store/DefsWCS.lean`), which kube-apiserver's index
functions meet.

## Notes

Test: [`k8s-watchcache-index-error-partial-update/index_error_test.go`](k8s-watchcache-index-error-partial-update/index_error_test.go)
(package `store`), run 2026-11-01 in a writable copy of
`k8s.io/apiserver@v0.0.0-20261021221356-9c4ec15b8038` (`GOWORK=off GOFLAGS=-mod=mod go test
./pkg/storage/cacher/store/ -run TestUpdateStoreIndexErrorLeavesElement -v`): it logs, without
failing, `BUG: the snapshot at revision 12 contains /bad, whose update at 11 failed` and `index
byName=bad has 0 items (the store has the element)`. The released v1.37.2 store differs
(`UpdateStoreLocked`) and was not checked. A cheap hardening: compute the index values before
touching the B-tree. Found 2026-10-26 reading `cacher/store` for KEP-6404.
