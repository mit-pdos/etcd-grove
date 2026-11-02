---
upstream: none
checked: 2026-11-01
links:
  - kubernetes/kubernetes#139657 pr open: the robustness test whose model backend first hit the read-side case (resource version "0")
blocks-proof: no
---

# client-go util/consistency: a resource version that does not parse passes `EnsureReady`, and one `WroteAt` cannot parse is not recorded

`ownerRecord.EnsureReady` skips (`continue`) a group resource whose store's last-synced resource
version fails `CompareResourceVersion` (not decimal, or with a leading `0`, `"0"` itself), so it
counts as ready whatever the store has seen; `ownerRecord.WroteAt` silently records nothing for a
version it cannot parse. Both fail open.

**Why not an issue:** not reachable for the resources the DaemonSet controller tracks, a
precondition kube-apiserver meets: for etcd-backed resources it serves etcd revisions (decimal, from
1), and an unsynced store (`""`) blocks. Only an aggregated API server or CRD backend with opaque or
zero versions, or a test fake (the robustness test's model backend, whose empty store answered
lists at `"0"`), reports one that does not parse; failing open there is presumably deliberate (an
unparseable version cannot be compared). At most a sentence in `EnsureReady`'s doc.

## Proof

no: the specs state the fail-open (`Spec/k8s_io/client_go/util/consistency/consistencyStore__EnsureReady.lean`,
`readyRec` in `Proof/k8s_io/client_go/util/consistency/Defs.lean`: "if `readRV` is well formed";
`consistencyStore__WroteAt.lean`, `wroteAtM` ignores a malformed version); the DaemonSet proof closes
it with a store contract that implies well-formed versions, which kube-apiserver's etcd revisions
meet.

## Notes

Code: `k8s.io/client-go/util/consistency/consistency.go` at `v0.0.0-20261021054439-569675c57fa3`
(`EnsureReady` around line 210, `WroteAt` around line 180). Found 2026-10-27 specifying
`util/consistency`, after the model finding of `issues/k8s-daemonset-ambiguous-create-duplicate-pod.md`.
