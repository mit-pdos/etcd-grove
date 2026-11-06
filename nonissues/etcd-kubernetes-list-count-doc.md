---
upstream: none
checked: 2026-11-05
links: []
blocks-proof: no
---

# client/v3/kubernetes: `ListResponse.Count` is documented over the prefix, counted from `Continue`

`kubernetes.ListResponse.Count` is documented as "the total number of keys with the specified
prefix, even if not all were returned due to a limit" (`client/v3/kubernetes/interface.go:113`).
When `ListOptions.Continue` is set, `Client.List` ranges from the continue key instead of the
prefix (`client.go:71-76`, `rangeStart`), so `Count` is the number of keys from the continue key to
the prefix's end.

**Why not an issue:** documentation only. The code's behaviour is what the one documented user
needs: Kubernetes' etcd3 store computes `hasMore` as `len(kvs) < count` per page
(`k8s.io/apiserver/pkg/storage/etcd3/store.go:893`) and the remaining item count from the same
per-page count (`PrepareContinueToken`, `store.go:865`), both correct only for the count from the
continue key.

## Proof

no: the spec of `kubernetes.Client.List` (k8s etcd3 stage 7e, `notes/k8s-etcd3-plan.md`, Q7e)
states the code's count, over `[start, prefixEnd)`.

## Notes

**Where:** etcd fork at the pin (`.lake/go-src/etcd`, `249d76bea7`), `client/v3/kubernetes`
`interface.go:113` (the doc) and `client.go:70-84` (`List`).

**Shown by** `examples/k8s/etcd3/revread_test.go` (`TestReadAtRevision`, its last part): with keys
`p/a`, `p/b`, `p/c`, `List("p/", {Limit: 1, Continue: "p/b"})` returns `p/b` with `Count` 2, not
3. The test passes (it checks the code's behaviour, not the doc's).

**Fix (documentation):** "Count is the number of keys in the requested range: from the prefix, or
from `Continue` if it is set, to the prefix's end, even if not all were returned due to a limit."
