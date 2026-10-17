---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#22516 issue open: this bug
  - etcd-io/etcd#22510 pr open: the fix (set `s.appliedIndex` in `applySnapshot`)
  - etcd-io/etcd#22527 pr open: related (its wait for apply ends at once in this state)
---

# etcdserver: `s.appliedIndex` stays behind the snapshot index after `applySnapshot`

- **Status**: a bug, known upstream.
- **Where**: `server/etcdserver/server.go:1001-1141` (`applySnapshot`, pinned `09669450f`): it
  sets `ep.appliedi` to the snapshot's index (`:1141`) but not `s.appliedIndex`, which only
  `applyEntries` sets; `applyAll` then triggers `s.applyWait` at `ep.appliedi` (`:984`).
- **What happens**: after a member installs a leader snapshot and before an entry after it is
  applied, `exceedsRequestLimit` compares the committed index (at least the snapshot's) with the
  stale `s.appliedIndex`, so every local proposal, the member's own publish included, is rejected
  with "too many requests", while `applyWait`'s waiters up to the snapshot index are released. With
  etcd-io/etcd#22527 the publish loop's wait (`applyWait.Wait(ci - 5000)`) then returns a closed
  channel at once and the loop spins: `notes/pr-verify/etcd-22527/server_publish_probe_test.go`,
  `TestPublishV3ProbeApplyWaitAheadOfAppliedIndex` (thousands of rejections in 100 ms on the PR head: 2519 and 22275 in two runs,
  `notes/pr-verify/etcd-22527/tests-pr-head.log`).
- **Expected**: `s.appliedIndex` is the index the apply loop has applied through, the snapshot's
  after a snapshot.
- **How the proof handles it**: outside the verified results: `applySnapshot` is proved only under
  raft's no-snapshot contract (`Proof/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__applySnapshot.lean`),
  under which `applyWait`'s `appliedAtLeast` and `s.appliedIndex` agree.
- **Possible fixes**: etcd-io/etcd#22510.
- **Found**: 2026-10-17, while verifying etcd-io/etcd#22527 (`pr-verify/etcd-22527`; the PR's
  description points at it).
