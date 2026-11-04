---
upstream: known
checked: 2026-11-04
links:
  - kubernetes/kubernetes#139252 issue open: this bug (the events etcd recreated empty)
  - kubernetes/kubernetes#139254 pr open: the fix, a regression test and an empty-response check
  - kubernetes/kubernetes#68172 issue closed: an older report of the same panic
blocks-proof: no
---

# k8s apiserver etcd3: the compactor panics when `compact_rev_key` disappears

`etcd3.Compact` (`k8s.io/apiserver/pkg/storage/etcd3/compact.go`) runs a transaction: if
`compact_rev_key`'s version equals the version this compactor last wrote, put the new revision;
otherwise get the key. On the else branch it reads `resp.Responses[0].GetResponseRange().Kvs[0]`
without checking that `Kvs` is non-empty. Once a compactor has written the key, its expected version
is at least 1. If the key then disappears (deleted, or etcd wiped, restored from a snapshot without
it, or recreated empty), the key's version is 0. The compare fails, the get returns no key-value,
and the compactor's goroutine panics with an index out of range, which crashes kube-apiserver. After
the restart, the expected version is 0 again and the next round succeeds.

**Why not an issue:** known upstream (kubernetes#139252, with the fix kubernetes#139254 open), and we
have no failing test of our own. The pinned apiserver (`examples/k8s/etcd3/go.mod`, pseudo-version
`v0.0.0-20261021221356-9c4ec15b8038`) still has the unchecked index. Found by code reading while
planning the compactor's proof (`notes/k8s-compactor-plan.md`).

## Proof

no: the compactor's specs will take it as the invariant that nothing deletes `compact_rev_key`. In the
plan's workloads, only compactors write it, and nothing deletes it or replaces the store. That is a
precondition a single etcd that is never reset meets. It is not the events-etcd deployment of
kubernetes#139252.
