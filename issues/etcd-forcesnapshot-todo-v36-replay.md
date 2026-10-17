---
upstream: unchecked
checked: 2026-10-17
links:
  - etcd-io/etcd#21574 pr open: does what the TODO says (backend flush in place of the forced disk snapshot) and so would lose the WAL snapshot record the downgrade needs; as written it hides this by taking a disk snapshot after every batch
---

# The `forceDiskSnapshot` TODO's assumption is false: a v3.6 member replays the pre-downgrade `ClusterVersionSet`

**Status**: documentation (a comment that plans an unsafe change), not a reachable bug in the pinned
code. The pinned code forces a disk snapshot after a downgrade, which is what makes the downgrade
work; the TODO on the flag proposes replacing it with a backend flush, on the assumption that v3.6
"bootstraps from db file". It does, for the cluster version and membership, but it still replays the
WAL from the latest WAL snapshot record, and that replay panics.

**Where**: `server/etcdserver/server.go` at the pinned fork revision `09669450f` (same upstream
`main` `10528e6f2`), the field `EtcdServer.forceDiskSnapshot` and its comment:

```go
// forceDiskSnapshot can force snapshot be triggered after apply, independent of the snapshotCount.
// Should only be set within apply code path. Used to force snapshot after cluster version downgrade.
// TODO: Replace with flush db in v3.7 assuming v3.6 bootstraps from db file.
forceDiskSnapshot bool
```

set by `ForceSnapshot` (called from `apply/backend.go`, `applierV3backend.ClusterVersionSet`, on a
cluster-version downgrade) and read by `shouldSnapshotToDisk`.

**What happens** if the forced disk snapshot is replaced by a backend flush: after a downgrade from
3.7 to 3.6 the latest WAL snapshot record can be before the `ClusterVersionSet{3.7}` entry. A member
restarted on the 3.6 binary replays that entry. v3.6's `applyInternalRaftRequest` applies
`ClusterVersionSet` whatever `shouldApplyV3` is (`release-3.6` `server/etcdserver/server.go:2042,2057`),
and `RaftCluster.SetVersion` calls `MustDetectDowngrade` (`release-3.6`
`server/etcdserver/api/membership/cluster.go:699`), which panics ("invalid downgrade; server version is
lower than determined cluster version") because 3.6 < 3.7. The storage-version downgrade
(`schema.UnsafeMigrate` with `MinimalEtcdVersion` of the entries after the snapshot) reads the same
entries.

Reproduction (etcd's own e2e test, with a 3.6.15 binary as `etcd-last-release`):
`TestDowngradeUpgradeClusterOf1` passes on upstream `10528e6f2` and on etcd-io/etcd#21574's head, and
fails with that panic on #21574 with `shouldSnapshotToDisk` restored to the snapshot-count rule alone
(`notes/pr-verify/etcd-21574/shouldSnapshotToDisk-fix.patch`, log
`notes/pr-verify/etcd-21574/e2e-downgrade.log`, in branch `pr-verify/etcd-21574`). The WAL-level probe
`notes/pr-verify/etcd-21574/downgrade_wal_test.go` shows the entry left after the latest snapshot record.

**Expected**: the comment should say why the forced snapshot is there (the WAL snapshot record must
move past the downgrade entry so that the older binary does not replay a `ClusterVersionSet` naming
the newer version), so that it is not replaced by a backend flush until the older binary no longer
replays it.

**How the proof handles it**: outside what is verified. On `lean`, `ForceSnapshot` is not translated
(names-only) and the apply package's contract for it (`isSnapshotServer`,
`Proof/go_etcd_io/etcd/server/v3/etcdserver/apply/Contracts.lean`) only says it returns; restart,
WAL replay and other binaries' versions are not modelled.

**Possible fixes**: reword the TODO; or, for the cleanup, keep a forced WAL snapshot on downgrade
(e.g. a forced disk snapshot as now) and drop only what is redundant.

**Found**: 2026-10-17, verifying etcd-io/etcd#21574 (`notes/pr-verify/etcd-21574.md`), by the review
of its `shouldSnapshotToDisk` spec.
