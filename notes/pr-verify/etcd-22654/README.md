# Reproduction & Test Artifacts for `etcd-io/etcd#22654`

This directory contains the reproduction test and test logs used in the verification report [`notes/pr-verify/etcd-22654.md`](../etcd-22654.md) for [`etcd-io/etcd#22654`](https://github.com/etcd-io/etcd/pull/22654) (`etcdserver: fix data race on the alarm store when applying a snapshot`).

## Contents

- [`repro_test.go`](./repro_test.go): The integration test `TestV3AlarmsDuringSnapshotInstall` (added in `tests/integration/v3_alarm_test.go` by the PR) that partitions a follower, commits 20 puts on the leader to trigger a snapshot (`SnapshotCount: 10`, `SnapshotCatchUpEntries: 5`), continuously calls `follower.Server.Alarms()` on a background goroutine while the partition heals and the follower installs the leader's snapshot, and verifies that the follower's backend was swapped (`oldBe != follower.Server.Backend()`).
- [`repro_test_before.log`](./repro_test_before.log): Output of `go test -race -v ./integration -run 'TestV3AlarmsDuringSnapshotInstall$' -count=1` (from `tests/`) with the `server/` changes of `8fd98af04` reverted. Fails with 3 `WARNING: DATA RACE` reports:
  1. Write to `s.alarmStore` in `(*EtcdServer).restoreAlarms()` (`server.go:2423`) vs read of `s.alarmStore` in `(*EtcdServer).Alarms()` (`server.go:2450`).
  2. Write to `a.mu` (`CompareAndSwapInt32` in `(*EtcdServer).Alarms() -> (*AlarmStore).Get()`) vs struct allocation/initialization in `v3alarm.NewAlarmStore()` (`alarms.go:48`) without a happens-before edge.
  3. Read of `a.types` in `(*AlarmStore).Get()` (`alarms.go:90`) vs write of `a.types` in `v3alarm.NewAlarmStore()` (`alarms.go:48`) without a happens-before edge.
- [`repro_test_after.log`](./repro_test_after.log): Output of `go test -race -v ./integration -run 'TestV3AlarmsDuringSnapshotInstall$' -count=1` (from `tests/`) on `pr-etcd-22654-goose-lean` (`e5553afdd0`). Passes with zero data races (`PASS: TestV3AlarmsDuringSnapshotInstall (0.43s)`).
- [`server_snapshot_test_after.log`](./server_snapshot_test_after.log): Output of `go test -race -v ./etcdserver -run 'TestSnapshotOrdering|TestConcurrentApplyAndSnapshotV3' -count=1` (from `server/`) on `pr-etcd-22654-goose-lean`. Both unit tests pass with `-race`.
