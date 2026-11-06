---
upstream: known
checked: 2026-11-04
links:
  - kubernetes/kubernetes#139252 issue open: this bug (the events etcd recreated empty)
  - kubernetes/kubernetes#139254 pr open: the fix, a regression test and an empty-response check
  - kubernetes/kubernetes#68172 issue closed: an older report of the same panic
blocks-proof: no
---

# apiserver etcd3: the compactor panics when `compact_rev_key` disappears from etcd

kube-apiserver's etcd compactor crashes the API server with an index out of range once the key it
coordinates through, `compact_rev_key`, has been written and then disappears: etcd wiped,
restored from a snapshot without it, recreated empty (an events etcd), or the key deleted. Its
next round expects the version it wrote, finds none, and indexes an empty Get response. After the
restart the compactor starts over at version 0 and runs again.

**Expected:** a compaction round should treat a missing `compact_rev_key` as a lost race and
start over (expect version 0 next round), as it does for any other version mismatch, rather than
crash the API server.

**Impact:** every kube-apiserver runs the compactor (`StartCompactorPerEndpoint`, the default
`--etcd-compaction-interval` of five minutes). A cluster whose etcd (or a separate events etcd) is
reset or restored under running API servers loses each of them once, at its next compaction
round. kubernetes#139252 reports it for an events etcd recreated empty.

**Reproduction:** `TestCompactMissingKey` in
[`issues/k8s-apiserver-compactor-missing-key-panic/compact_missing_key_test.go`](k8s-apiserver-compactor-missing-key-panic/compact_missing_key_test.go),
copied into `pkg/storage/etcd3` of a writable copy of
`k8s.io/apiserver@v0.0.0-20261021221356-9c4ec15b8038` (kubernetes/apiserver@9c4ec15b8038, the
pin of `examples/k8s/etcd3/go.mod`, 2026-10-21), go1.27.1 linux/amd64:

```
$ go test ./pkg/storage/etcd3 -run TestCompactMissingKey -count=1
--- FAIL: TestCompactMissingKey (0.66s)
    compact_missing_key_test.go:27: Compact panicked once compact_rev_key was deleted: runtime error: index out of range [0] with length 0
FAIL
```

The example `examples/k8s/compactor` reproduces it the way an API server runs the compactor
(`NewCompactor`, a real clock): `TestMissingKey` deletes the key once a compactor has written it,
and the compactor's goroutine panics.

**Cause:** [`Compact`](https://github.com/kubernetes/apiserver/blob/9c4ec15b8038/pkg/storage/etcd3/compact.go#L219-L240)
runs a transaction: if the key's version is the expected one, put the new revision, else get the
key. On the else branch it reads `resp.Responses[0].GetResponseRange().Kvs[0]`
([L234-L235](https://github.com/kubernetes/apiserver/blob/9c4ec15b8038/pkg/storage/etcd3/compact.go#L234-L235))
without checking that the Get returned a key-value. Once a compactor has written the key its
expected version is at least 1, and a missing key's version is 0, so the compare fails and the Get
returns nothing.

## Proof

no: the compactor's specs (`Proof/k8s_io/apiserver/pkg/storage/etcd3/CompactorDefs.lean`, `casOk`)
take from their caller that a round's failing transaction finds the key holding a recorded
revision: nothing deletes `compact_rev_key`. In the plan's workloads (`examples/k8s/compactor`)
only compactors write it, and nothing deletes it or replaces the store, a precondition a
Kubernetes etcd that is never reset meets (its keyspace is the API servers'). Found by code reading
while planning the compactor's proof (`notes/k8s-compactor-plan.md`); the test was written in its
K3.
