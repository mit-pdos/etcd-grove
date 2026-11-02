---
upstream: reported
checked: 2026-11-01
links:
  - etcd-io/etcd#22653 issue open: this bug
  - etcd-io/etcd#22654 pr open: the fix (`AlarmStore.Recover`), ok-to-test, reviewed by serathius
  - etcd-io/etcd#22609 pr merged: the same class (mvcc `Hash` racing with `Restore`'s backend swap); a different field
  - etcd-io/etcd#10874 pr closed: `s.be` read outside `bemu` in `applySnapshot`; not the alarm store
blocks-proof: yes
---

# server: data race on a member's alarms between Status and applying a leader's snapshot

Reading a member's alarms, as the maintenance `Status` RPC and the `/health`, `/livez` and
`/readyz` handlers do, races with the member applying a snapshot sent by the leader:
`applySnapshot` replaces the alarm store with a new one, unlocked, while those goroutines read it.
A reader can see a stale or empty alarm list for a moment; no crash found.

**Reproduction:** `TestV3AlarmsDuringSnapshotInstall` in
[`issues/etcd-alarm-store-snapshot-race/alarms_snapshot_test.go`](etcd-alarm-store-snapshot-race/alarms_snapshot_test.go),
copied into `tests/integration` at etcd-io/etcd@1573d5941 (2026-10-28), go1.27.3 linux/amd64. A
follower is partitioned while the leader commits 20 puts (`SnapshotCount: 10`,
`SnapshotCatchUpEntries: 5`); a goroutine reads the follower's `Server.Alarms()` while the
partition heals and the follower applies the snapshot:

```
$ go test -race ./integration -run '^TestV3AlarmsDuringSnapshotInstall$' -count=1
WARNING: DATA RACE
Write at 0x00c00105daa8 by goroutine 627:
  sync/atomic.CompareAndSwapInt32()
  go.etcd.io/etcd/server/v3/etcdserver.(*EtcdServer).Alarms()
      server/etcdserver/server.go:2426 +0xdd
  go.etcd.io/etcd/tests/v3/integration.TestV3AlarmsDuringSnapshotInstall.func1()
Previous write at 0x00c00105daa8 by goroutine 343:
  go.etcd.io/etcd/server/v3/etcdserver/api/v3alarm.NewAlarmStore()
      server/etcdserver/api/v3alarm/alarms.go:48 +0xb3
  go.etcd.io/etcd/server/v3/etcdserver.(*EtcdServer).restoreAlarms()
      server/etcdserver/server.go:2395 +0x128
  go.etcd.io/etcd/server/v3/etcdserver.(*EtcdServer).applySnapshot()
      server/etcdserver/server.go:1102 +0x1679
...
--- FAIL: TestV3AlarmsDuringSnapshotInstall (0.51s)
    testing.go:1867: race detected during execution of test
FAIL	go.etcd.io/etcd/tests/v3/integration	1.141s
```

## Proof

yes: the verified fork carries the PR's fix (`8fd98af04`, `AlarmStore.Recover`, `etc/goose.py`);
without it the server's invariant that the alarm-store field is read-only
(`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvApplier.lean`) fails once a member installs a
snapshot, and a racy reader cannot be verified.

## Fix

**Branch**: `fix/etcd-alarm-store-snapshot-race` in `~/etcd-fixes/etcd-alarm-store-snapshot-race` (upamanyus/etcd, pushed): 9e75921f5 test, 8938e98c2 fix
**Base**: etcd-io/etcd@3aaab3479b6c4f5fe1b2b8f33437093c2caae88a

The PR (#22654) is open with those two commits. The local branch has a newer, unpushed revision of
the test commit (8ca29584f; fix 098754afe): it drops the `NotSame` backend check and rewords the
comments, apparently in answer to serathius's open review question on the test ("What this test
validates?"); push it with a reply, or drop it.

## Notes

The 2026-10-23 review's plan: upstream (done).
