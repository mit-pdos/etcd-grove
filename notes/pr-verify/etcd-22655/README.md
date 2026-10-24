# Reproduction and Probe Artifacts for `etcd-io/etcd#22655`

This directory contains the Go unit tests and execution logs used to verify `etcd-io/etcd#22655` (`etcdserver: fill backend-ahead WAL gap with no-op entries on force-new-cluster`, fixing `etcd-io/etcd#22646`).

## Files

- `bootstrap_pr22655_probe_test.go` — Go test suite run in `server/etcdserver` on `/root/etcd-pr/etcd-22655`:
  1. `TestBootstrapWALFromSnapshotBackendAheadOfWAL`: The PR's regression test (snapshot at index `27`, WAL entries `28..31` with `HardState.Commit = 28`, backend `consistentIndex = 49`, `ForceNewCluster = true`), augmented to also call `bwal.MemoryStorage()` (`ms.LastIndex() == 51`) and log the difference between in-memory `bwal.st.GetCommit()` (`51`) and on-disk `st2.GetCommit()` (`28`).
  2. `TestProbePreFixMemoryStoragePanicsOnGap`: Reproduces the pre-PR#22655 failure mode (`etcd-io/etcd#22646`) by running the `ForceNewCluster` sequence without `fillBackendAheadGap()`. Confirms both failure stages:
     - `bwal.ents` has `[28, 29, 30, 31, 50, 51]` (length `6`, non-contiguous), so `bwal.MemoryStorage().LastIndex()` is `27 + 6 = 33 != 51`, and `raft.RestartNode` panics in `loadState` (`state.commit 51 is out of range [27, 33]`).
     - Reopening the WAL on disk (`w2.ReadAll()`) fails with `wal.ErrSliceOutOfRange` (`wal: slice bounds out of range`), permanently bricking the member's WAL directory.
  3. `TestProbeMembershipChangeInBackendAheadGap`: Demonstrates an edge case when a membership change (e.g., adding node `3`) occurred in the backend-ahead gap (`32..49`): because `fillBackendAheadGap` fills `32..49` with empty `EntryNormal` entries, `GetEffectiveNodeIDsFromWALEntries` only sees the snapshot's `ConfState` (`Voters: [1, 2]`) and only generates `ConfChangeRemoveNode(2)` (not `ConfChangeRemoveNode(3)`).
- `probe-test.log` — Output of `GOTOOLCHAIN=go1.27.1 go test -v -run 'TestBootstrapWALFromSnapshotBackendAheadOfWAL|TestProbe' ./etcdserver`.
