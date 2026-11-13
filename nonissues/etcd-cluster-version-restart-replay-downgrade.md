---
upstream: none
checked: 2026-11-06
links:
blocks-proof: no
---

# etcdserver: a restarted member replaying an old cluster-version entry logs a "downgrade", forces a snapshot and briefly reports the older cluster version

At a restart a member loads the cluster version from its backend (the version at the backend's
consistent index), then replays the committed entries from its last WAL snapshot up to that index
without applying them to the backend again. If the cluster version was raised inside that range (an
older `ClusterVersionSet` entry followed by a newer one, both at or below the consistent index), the
replay of the older entry sets the in-memory cluster version back to it, logs "Cluster version
downgrade detected, forcing snapshot" and forces a disk snapshot; the replay of the newer entry,
later in the same range, sets it forward again. Meanwhile the member reports the older version (the
`/version` endpoint) and, when the older version is exactly one minor version below, runs with that
version's capabilities.

**Why not an issue:** no test, found by code reading; no wrong result: the backend is not written
(the replay is `ApplyV2storeOnly`), the version reported in the meantime is the one the cluster had
at the entry being replayed (what a member lagging at that index reports), the forced snapshot is an
extra snapshot at the member's applied index, and the newer entry's replay restores the version
before the member applies anything new.

## Proof

no: the server's rest model has no in-memory cluster version (`restSetVersion` at `v3 = false` is
the identity, `Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/RestModel.lean:110-111`), and the
forced snapshot is one more disk snapshot at Go's applied index, which the restart's window design
covers (`notes/restart-plan.md`, "R2d' Scope (approved 2026-11-06)").

## Notes

The path, at etcd `673da07c8` (`server/` paths):
- The version at the consistent index: `bootstrappedCluster.Finalize` calls `cl.Recover`
  (`etcdserver/bootstrap.go:514`), which loads `c.version` from the backend
  (`etcdserver/api/membership/cluster.go:256-257`, `UnsafeLoad`). Go's applied index starts at the
  WAL snapshot's index, below it, and raft hands the committed entries again from there.
- The replay: `apply` takes `shouldApplyV3 = ApplyV2storeOnly` for an entry at or below the
  consistent index (`etcdserver/server.go:1939-1944`) and calls `applyEntryNormal(e, false)`
  (`:1948`), which runs `apply.Apply` (`:2000`; `etcdserver/apply/apply.go:27-49`: a
  `ClusterVersionSet` has side effects, so it goes to the applier); `dispatch` handles
  `ClusterVersionSet` before its `!shouldApplyV3` return (`etcdserver/apply/uber_applier.go:105-109`,
  `:126-128`).
- The "downgrade": `applierV3backend.ClusterVersionSet` reads the current (newer) version, calls
  `SetVersion`, and on a lower version logs and calls `ForceSnapshot`
  (`etcdserver/apply/backend.go:270-285`). `SetVersion` sets `c.version` unconditionally
  (`cluster.go:608-609`), writes the backend only if `shouldApplyV3` (`:613-615`), notifies the
  version watchers and calls `onSet` = `api.UpdateCapability` (`:620-623`), which lowers the
  capabilities only for a one-minor-version downgrade (`etcdserver/api/capability.go:63-75`,
  `etcdserver/version/downgrade.go:37-39`, `:68-76`). `MustDetectDowngrade` (`cluster.go:611`) does
  not panic on a lower cluster version (`downgrade.go:42-55`).
- The snapshot: `ForceSnapshot` sets `forceDiskSnapshot` (`server.go:1241-1243`), and at the end of
  the batch `snapshotIfNeededAndCompactRaftLog` (`:1007`) takes a disk snapshot at Go's applied index
  whenever it moved past the last disk snapshot (`:1256-1258`, `:2113-2137`).

Related: `etcd-cluster-version-stale-proposal-downgrade` (the same applier branch, reached by two
proposals applied out of order, where the lowering is not undone by a later entry). Upstream
searched (GitHub issue search, "downgrade detected", "ClusterVersionSet restart", "cluster version
replay restart"): nothing on this.
