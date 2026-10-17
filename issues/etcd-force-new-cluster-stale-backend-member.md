---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#21867 pr open: fixes it (removes every other member from the backend in `Finalize`), but introduces a transport regression (notes/pr-verify/etcd-21867.md)
  - etcd-io/etcd#20967 issue closed: the v2store/v3store inconsistency that leaves such members in the backend; its discussion says `--force-new-cluster` should clean up from v3store
---

# `--force-new-cluster` cannot elect when the backend has a member the WAL does not know

**Status**: a bug (an availability failure of the recovery path), in code outside the verified
results: `bootstrap.go`'s force-new-cluster path is not translated with bodies.

**Where** (the fork's `goose-lean` at `09669450f`, the pin in `etc/goose.py`):
- `server/etcdserver/bootstrap.go:612-640` (`bootstrapWALFromSnapshot`, `cfg.ForceNewCluster`):
  the conf-change entries appended are `CreateConfigChangeEnts` of
  `GetEffectiveNodeIDsFromWALEntries(wal.snapshot, wal.ents)` (`bootstrap.go:754-762`): one
  `ConfChangeRemoveNode` per id known to the WAL's snapshot `ConfState` and its conf-change
  entries;
- `server/etcdserver/bootstrap.go:107-118` and `132-148` (`buildConfStateFromV3store`): raft's
  starting `ConfState` is built from the **backend's** `members` bucket.

**What happens**: a member that is in the backend's `members` bucket but in neither the WAL's
snapshot nor its entries (etcd-io/etcd#20967 shows how upgraded clusters end up with such
members) becomes a voter of the restarted node's raft configuration, and no entry removes it.
The force-new-cluster node, alone, needs that voter's vote and never becomes leader.

Reproduction: `notes/pr-verify/etcd-21867/force_new_cluster_stale_member_test.go`
(`TestForceNewClusterWithStaleBackendMember`, in `tests/integration`): a 3-member cluster, member
0 stopped, a member `0x42` written into its backend only, member 0 restarted with
`ForceNewCluster`. On upstream `9ed485d3e` (the PR's base) the test times out (2 minutes) with
raft at `voters=(42 456b3f7378cc0091)` (`notes/pr-verify/etcd-21867/base-stale.log`); with
etcd-io/etcd#21867 applied it passes.

**Expected**: `--force-new-cluster` ("Force to create a new one member cluster") leaves a
one-member cluster whatever the backend's membership holds.

**How the proof handles it**: not reached: `bootstrap`, `bootstrapWALFromSnapshot` and
`buildConfStateFromV3store` are not translated; the pr-verify branch's `Finalize` spec
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/bootstrappedCluster__Finalize.lean`) shows that with
the PR the backend's members after `Finalize` are this node at most (`finalize_force_only_self`,
`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvFinalize.lean`).

**Possible fixes**: append removal entries for the backend's members too (the union of the WAL's
ids and the backend's), so that the usual apply path removes them from raft, the backend and the
transport alike; or, as etcd-io/etcd#21867 does, delete the other members from the backend in
`Finalize`, which needs `applyConfChange` to still call `RemovePeer` for the removal entries it then
rejects (see `notes/pr-verify/etcd-21867.md`).

**Found**: 2026-10-17, verifying etcd-io/etcd#21867 (pr-verify), by a Go integration test.
