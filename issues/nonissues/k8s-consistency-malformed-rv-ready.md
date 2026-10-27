---
upstream: unchecked
checked: 2026-10-27
links:
  - kubernetes/kubernetes#139657 pr open: the robustness test whose model backend first hit the read-side case (resource version "0")
---

# k8s.io/client-go/util/consistency: a resource version that does not parse passes `EnsureReady`, and one that `WroteAt` cannot parse is not recorded

**Not an issue (2026-10-27).** Both are fail-open paths of the consistency store, stated in its
verified specs, but neither is reachable over a real kube-apiserver for the resources the DaemonSet
controller tracks (pods, daemonsets), whose resource versions are etcd revisions. Filed here so the
behavior is on record; revisit if the store is used for resources whose versions are opaque.

**Status**: undocumented behavior (fail-open), not a bug for its users.

**Where**: `k8s.io/client-go/util/consistency/consistency.go` at the client-go pin of
`examples/k8setcd3/go.mod` (`v0.0.0-20261021054439-569675c57fa3`, byte-identical to
kubernetes/kubernetes#139657's head `13ecb9cc`):

- `ownerRecord.EnsureReady` (line ~210): `i, err := resourceversion.CompareResourceVersion(wroteRV,
  readRV); if err != nil { continue }`. The recorded `wroteRV` is always well formed (below), so the
  comparison fails exactly when the store's `LastStoreSyncResourceVersion()` is not a well-formed
  version: not a decimal string, or with a leading `0` (`"0"` itself). Such a group resource
  counts as ready, whatever the store has seen. `""` (an unsynced store) and a missing store do
  block.
- `ownerRecord.WroteAt` (line ~180): a version `CompareResourceVersion` rejects (`""`, `"0"`, a
  non-decimal one) is silently not recorded, though the owner's record is still created, or
  replaced for a new UID; `EnsureReady` then has nothing to wait for.

**What happens**: with a store reporting `"0"` (an informer whose only sync was a list answered with
resource version `"0"`), `EnsureReady` returns `nil` for an owner whose recorded write the store
has not seen. This is how the DaemonSet robustness test's model backend lost the KEP-5647 check
(`issues/upstream/k8s-daemonset-ambiguous-create-duplicate-pod/meta.md`, "Model findings", 1: the
model's empty store answered lists with `"0"`; the model now starts at 1).

**Why it is not reachable here**: the store's resource version comes from the reflector
(`tools/cache/thread_safe_store.go`): `Replace(items, rv)` with the list's `ResourceVersion`,
`Bookmark(rv)` with a bookmark's, and `Add`/`Update`/`DeleteWithObject` with the object's. For
etcd-backed resources kube-apiserver serves etcd revisions (decimal, from 1: etcd's revision starts
at 1, and lists from the watch cache carry the cache's revision, initialized from an etcd list), and
objects' versions are their mod revisions. A server that answers `""` makes the store block (fail
safe). Only an aggregated API server or a CRD backend with opaque or zero resource versions, or a
test fake, can report one that does not parse; client-go's `resourceversion` package documents that
comparisons have meaning only for one resource, and failing open there is presumably deliberate (an
unparseable version cannot be compared). The `WroteAt` side likewise needs a write that returned a
malformed version.

**Expected**: the `EnsureReady` doc ("returns nil if observed resource versions are at least as new
as any recorded versions") suggests a comparison failure would not count as "at least as new". A
sentence in the doc would make the fail-open explicit.

**How the proof handles it**: the specs state it.
`Spec/k8s_io/client_go/util/consistency/consistencyStore__EnsureReady.lean` returns `nil` only with
`readyRec` (`Proof/k8s_io/client_go/util/consistency/Defs.lean`), whose clause for a recorded
`wroteRV` is "a store is registered and returned a non-empty `readRV` with the caller's contract
`G gr readRV`, and **if `readRV` is well formed**, `decVal wroteRV ≤ decVal readRV`";
`consistencyStore__WroteAt.lean` updates the abstract state by `wroteAtM` (`Model.lean`), which ignores
a malformed `rv`. A downstream proof (the DaemonSet controller's) closes the hole by choosing `G` to
imply that `readRV` is well formed (the model API server's versions are `strconv.FormatUint` of a
counter from 1) and by showing that every recorded version is a created object's.

**Possible fixes**: document both cases; or treat a comparison error in `EnsureReady` as not ready
(fail safe), at the cost of blocking forever on a resource with opaque versions.

**Found**: 2026-10-27, specifying `util/consistency` (branch `k8s-leaf-cache`), after the model
finding above.
