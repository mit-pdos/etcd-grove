---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# cache: `Cache.Get` with `WithKeysOnly` returns values

[`validateGet`](https://github.com/etcd-io/etcd/blob/a4d2bb1720b9/cache/cache.go#L448-L476) rejects
the options the cache does not serve (`WithCountOnly`, `WithPrevKV`, `WithSort`, `WithLimit`, the
revision filters) with `ErrUnsupportedRequest`, but neither rejects nor honours `WithKeysOnly`:
[`snapshot.Range`](https://github.com/etcd-io/etcd/blob/a4d2bb1720b9/cache/snapshot.go#L33-L55)
returns the stored key-values with their values. A keys-only `Get` of the cache answers differently
from the same `Get` of the client (which returns empty values), although the cache is used as a
drop-in `Getter` (etcd's `tests/integration/cache_test.go` runs one `testGet` against both).

**Why not an issue:** no test; found by code reading (batch 1g of the specs-only branch). No caller
in etcd, this repository's examples or Kubernetes passes `WithKeysOnly` to the cache, so no user is
affected today; it is a documentation / behaviour mismatch (`ErrUnsupportedRequest`'s comment names
the unhandled options). A test could promote it: a cache `Get(key, WithKeysOnly())` after a `Put`
with a non-empty value, expecting an empty value or `ErrUnsupportedRequest`.

## Proof

no: the cache's `Get` spec (`SpecPlan/Spec/go_etcd_io/etcd/cache/v3/Cache__Get.lean`, specs-only branch)
states what the code does: `getUnsupported` omits keys-only and the answer is the full key-values.

## Notes

Fix, if wanted: reject `WithKeysOnly` in `validateGet` (`ErrUnsupportedRequest`), or blank the
values in `Get`'s response.
