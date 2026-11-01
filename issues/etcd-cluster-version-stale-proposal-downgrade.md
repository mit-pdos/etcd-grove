---
upstream: unchecked
---

# Stale `ClusterVersionSet` proposals can apply out of order: the cluster version regresses and a snapshot is forced

**Status**: a possible wrong result (unchecked in a real cluster). The cluster version can move
down, and a disk snapshot be forced, without any downgrade being enabled. This was found by reading
the code while specifying the server's snapshot path; it has not been reproduced.

**Where** (the fork `upamanyus/etcd`, branch `goose-lean`, `etc/goose.py`'s pin):
- `server/etcdserver/version/monitor.go:56-104`, `UpdateClusterVersionIfNeeded` and
  `decideClusterVersion`. The leader's monitor decides the next cluster version from its *own read*
  of the current one:
  - while the cluster version is nil, it proposes the members' minimal server version, or
    `MinClusterVersion` (3.0.0) when some member's version is unknown;
  - otherwise, with no downgrade enabled, it proposes only a strict upgrade
    (`cv < minimal && IsValidClusterVersionChange`).
- `server/etcdserver/adapters.go:44-46`. `UpdateClusterVersion` proposes in a goroutine
  (`s.GoAttach(func() { s.updateClusterVersionV3(version) })`).
- `server/etcdserver/server.go:2318-2337`. `updateClusterVersionV3` proposes
  `ClusterVersionSet{Ver: v}` through `raftRequest`, with no check at proposal time.
- `server/etcdserver/apply/backend.go:270-284`, `applierV3backend.ClusterVersionSet`. The applier
  sets the version unconditionally (`Cluster.SetVersion`, `membership/cluster.go:589`). If the new
  version is lower than the previous one, it logs "Cluster version downgrade detected" and calls
  `SnapshotServer.ForceSnapshot()`.

**What happens**: the decision is made against the version the monitor read, not the version at
apply time, so two proposals in flight can be applied out of order. Example:
1. The cluster version is nil and some member's version is not yet known. A monitor tick proposes
   3.0.0, from goroutine G1.
2. A later tick sees the versions; the cluster version is still nil, since G1's entry is not applied
   yet. It proposes V, from goroutine G2.
3. If G2's entry is committed before G1's, the cluster version becomes V and then 3.0.0. The second
   apply takes the downgrade branch: a regression V → 3.0.0, and `ForceSnapshot`.

How the two proposals can be reordered:
- G1 and G2 are separate goroutines (`GoAttach`). Each `raftRequest` waits up to `ReqTimeout`, for
  example while proposals are dropped or blocked during a leader change, so both can be in flight.
- Two successive leaders' monitors, each acting on a stale read, can also do it.
- The same shape is possible with two stale upgrade proposals during a rolling upgrade.

A regressed cluster version also changes which features the cluster enables (the capability map
follows the cluster version) until the next tick raises it again.

**Sure**: the code paths above. There is no apply-time check that a `ClusterVersionSet` does not
lower the version (outside an enabled downgrade). `ForceSnapshot` is called on any lowering.

**Unchecked**:
- whether the reordering is reachable in a real cluster (timing: the monitor's interval against
  `ReqTimeout`, and whether a leader's dropped proposals can be re-proposed late);
- whether etcd guards it elsewhere, for example by the monitor running only once the cluster version
  is set, or by some ordering of `raftRequest`s from one member;
- whether upstream knows of it.

**Reproduction**: none yet. A unit test could show each half separately:
- `decideClusterVersion` proposing 3.0.0 and then V across two ticks while the version is nil;
- `ClusterVersionSet` with a lower version calling `ForceSnapshot`.

The interleaving itself needs an integration test that delays one `raftRequest` past the next tick,
for example with a failpoint in `updateClusterVersionV3`. That is not cheap, so it was not done.

**Expected**: the cluster version only moves down through an enabled downgrade (`DowngradeInfoSet`),
as `decideClusterVersion` intends.

**How the proof handles it**: the server's request model admits any `ClusterVersionSet` whose
version parses (`monitorClusterVersions`' contract, `Proof/.../etcdserver/InvMonitors.lean:58`), so
the downgrade branch and its `ForceSnapshot` are reachable in the model
(`apply/applierV3backend__ClusterVersionSet.lean:88`). This is why the repair's D2 option (a), a run
bound below `memorySnapshotCount`, does not by itself make the snapshot path unreachable
(`notes/raft-unified-plan.md`, "Repair: Stage F statements").

**Possible fixes**:
- In the applier, ignore (or reject) a `ClusterVersionSet` that lowers the version unless a
  downgrade is enabled and its target is that version.
- Or have the proposer carry the version it read, and the applier apply it only if it is still the
  current one (a compare-and-set).

**Found**: 2026-10-30, Stage F of the server repair, checking whether `ForceSnapshot` is reachable.
