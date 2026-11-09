---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# k8s etcd3 store: a past-revision List whose resource version is at least 2^63 returns the latest list instead of a too-large error

`storage.ValidateListOptions` (`k8s.io/apiserver/pkg/storage/interfaces.go:399-405`, apiserver
`9c4ec15b8038`) converts the parsed resource version to the read revision with
`withRev = int64(parsedRV)` for `ResourceVersionMatchExact`, and for the legacy match when
recursive with a limit. `APIObjectVersioner.ParseResourceVersion` accepts any `uint64`
(`api_object_versioner.go:90-103`, `strconv.ParseUint(rv, 10, 64)`), so a resource version in
`[2^63, 2^64)` (e.g. `"18446744073709551615"`) gives a negative `withRev`. `pagedChunks`
(`etcd3/store.go:881-920`) passes it to `kubernetes.Client.List` as the range's revision, and etcd
reads a revision `<= 0` as the current one (`server/storage/mvcc/kvstore_txn.go:75-80`), so no
`ErrFutureRev` comes back: `GetList` returns the latest list, and `finalizeList` labels it with
`uint64(withRev)`, the requested resource version. For a resource version above the current
revision but below 2^63 the same call returns `TooLargeResourceVersion` (`listReadError`).

**Why not an issue:** found by code reading of the etcd3 store, no Go test; whether a request
through the apiserver reaches the store with such a resource version (the cacher's delegation of
`Exact` lists) was not checked. Found while proving k8s etcd3 stage 7e-2 (`GetList.spec`'s
past-read branch: `notes/k8s-7e-2-draft.md`). Upstream not searched.

## Proof

no: `store.GetList.spec` takes a premise bounding the parsed resource version below 2^63 (proposed
to etcd-grove-81, 2026-11-09), which the driver meets: its resource versions are revisions of the
run and small offsets from them (`minRV`).
