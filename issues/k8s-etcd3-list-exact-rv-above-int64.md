---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# apiserver etcd3: a list at a resource version of 2^63 or more returns the current objects instead of a "too large resource version" error

A list request with `resourceVersionMatch=Exact` (or the legacy match with a limit) and a
`resourceVersion` between 2^63 and 2^64-1, served by the etcd3 storage without the watch cache,
succeeds and returns the current objects labelled with the requested resource version, when the
`EtcdRangeStream` feature is off. With it on (the default) the request fails with an internal error
("etcd returned revision 2 for a list read at revision -1"). A resource version above the current
revision but below 2^63 fails, as it should, with a "too large resource version" error.

**Expected:** a list at a resource version the storage has not reached should fail with a "too
large resource version" error (`storage.NewTooLargeResourceVersionError`, which `listReadError`
returns for any such revision below 2^63,
[`store.go#L922-L934`](https://github.com/kubernetes/apiserver/blob/9c4ec15b8038/pkg/storage/etcd3/store.go#L922-L934)),
whatever the number.

**Impact:** any client can send such a resource version; the list validation does not bound it
([`validation.go`](https://github.com/kubernetes/apimachinery/blob/0b7d352f711c/pkg/apis/meta/internalversion/validation/validation.go#L28-L50)).
It needs the etcd3 storage to serve the list itself (watch cache disabled for the resource, or a
list the cache delegates). The answer is a list of the current state claiming a resource version no
object can have; a client that trusts it (a reflector resuming from it, a consistency check) is
misled. With `EtcdRangeStream` on, the client gets a 500 instead of a 504. Low impact: no real
client sends such a resource version.

**Reproduction:** `TestListResourceVersionAboveInt64` in
[`issues/k8s-etcd3-list-exact-rv-above-int64/list_rv_above_int64_test.go`](k8s-etcd3-list-exact-rv-above-int64/list_rv_above_int64_test.go),
copied into `pkg/registry/generic/registry` of a writable copy of
`k8s.io/apiserver@v0.0.0-20261021221356-9c4ec15b8038` (kubernetes/apiserver@9c4ec15b8038, the pin
of `examples/k8s/etcd3/go.mod`, 2026-10-21), go1.27.1 linux/amd64. It lists through the registry's
`Store` (after the list handler's `ValidateListOptions`) backed by the etcd3 storage with the watch
cache off, as `newTestGenericStoreRegistry(t, scheme, false)` builds it, once with
`EtcdRangeStream` on and once off:

```
$ go test ./pkg/registry/generic/registry -run TestListResourceVersionAboveInt64 -count=1
--- FAIL: TestListResourceVersionAboveInt64/RangeStream/exact,_2^64-1
    list_rv_above_int64_test.go:64: resourceVersion=18446744073709551615: expected a too-large resource version error, got etcd returned revision 2 for a list read at revision -1
--- FAIL: TestListResourceVersionAboveInt64/paginated/exact,_2^64-1
    list_rv_above_int64_test.go:59: resourceVersion=18446744073709551615: expected a too-large resource version error, got 1 items at resourceVersion "18446744073709551615"
--- FAIL: TestListResourceVersionAboveInt64/paginated/exact,_2^63
    list_rv_above_int64_test.go:59: resourceVersion=9223372036854775808: expected a too-large resource version error, got 1 items at resourceVersion "9223372036854775808"
--- FAIL: TestListResourceVersionAboveInt64/paginated/legacy_with_limit,_2^64-1
    list_rv_above_int64_test.go:59: resourceVersion=18446744073709551615: expected a too-large resource version error, got 1 items at resourceVersion "18446744073709551615"
FAIL
```

(The `exact, 10^6` cases pass in both modes: a too-large error.)

**Cause:** `storage.ValidateListOptions` turns the parsed `uint64` resource version into the read
revision with `withRev = int64(parsedRV)`
([`interfaces.go#L399-L405`](https://github.com/kubernetes/apiserver/blob/9c4ec15b8038/pkg/storage/interfaces.go#L399-L405)),
negative from 2^63 on, and `APIObjectVersioner.ParseResourceVersion` accepts any `uint64`
([`api_object_versioner.go#L90-L103`](https://github.com/kubernetes/apiserver/blob/9c4ec15b8038/pkg/storage/api_object_versioner.go#L90-L103)).
etcd reads a range revision `<= 0` as the current one, so no "future revision" error comes back:
the paginated path stamps each page with `withRev` and `finalizeList` labels the list with
`uint64(withRev)`; the RangeStream path sees etcd's real revision differ from `withRev` and fails
([`store.go#L829-L838`](https://github.com/kubernetes/apiserver/blob/9c4ec15b8038/pkg/storage/etcd3/store.go#L828-L838)).

## Proof

no: `store.GetList.spec` takes the premise `uint.Z n < 2 ^ 63` on the parsed resource version
(`notes/k8s-7e-2-draft.md`, "Corrections (2026-11-09)", G1), which the driver meets (its resource
versions are revisions of the run and small offsets, `minRV`).

## Fix

Not written. `ValidateListOptions` (or the versioner) would reject a resource version above
`math.MaxInt64` with a "too large resource version" error, or the read revision would be checked
before the conversion.
