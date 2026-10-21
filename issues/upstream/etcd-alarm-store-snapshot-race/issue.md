Title: Data race on a member's alarms between Status and applying a leader's snapshot

### What happened?

A member that applies a leader's snapshot while it serves the maintenance `Status` RPC has a data race on its alarms. Under `go test -race`:

1. Three members; one follower is partitioned from the other two.
2. The leader takes 20 puts, enough to compact its log past the follower's index (`SnapshotCount: 10`, `SnapshotCatchUpEntries: 5`).
3. Clients keep calling `Status` on the follower while the partition heals and the follower applies the leader's snapshot.

The race detector reports (output trimmed):

```
WARNING: DATA RACE
Write at 0x00c00059c5b0 by goroutine 379:
  go.etcd.io/etcd/server/v3/etcdserver.(*EtcdServer).restoreAlarms()
      /home/ubuntu/etcd-fixes/etcd-alarm-store-snapshot-race/server/etcdserver/server.go:2399 +0x144
  go.etcd.io/etcd/server/v3/etcdserver.(*EtcdServer).applySnapshot()
      /home/ubuntu/etcd-fixes/etcd-alarm-store-snapshot-race/server/etcdserver/server.go:1102 +0x1679
  ...

Previous read at 0x00c00059c5b0 by goroutine 875:
  go.etcd.io/etcd/server/v3/etcdserver.(*EtcdServer).Alarms()
      /home/ubuntu/etcd-fixes/etcd-alarm-store-snapshot-race/server/etcdserver/server.go:2426 +0x2e
  go.etcd.io/etcd/server/v3/etcdserver/api/v3rpc.(*maintenanceServer).Status()
      /home/ubuntu/etcd-fixes/etcd-alarm-store-snapshot-race/server/etcdserver/api/v3rpc/maintenance.go:301 +0xa7e
  ...
--- FAIL: TestV3AlarmsDuringSnapshotInstall (0.59s)
    testing.go:1867: race detected during execution of test
```

The `/health` and `/readyz` handlers read the alarms the same way, so any member that applies a leader's snapshot while it answers `Status` or a health check races.

### What did you expect to happen?

Applying a snapshot should not race with `Status` or the health checks: they should see the alarms from before or after the snapshot.

### How can we reproduce it (as minimally and precisely as possible)?

Integration test: [`TestV3AlarmsDuringSnapshotInstall`](https://github.com/upamanyus/etcd/blob/fix/etcd-alarm-store-snapshot-race/tests/integration/v3_alarm_test.go#L161-L202) on branch [`upamanyus/etcd:fix/etcd-alarm-store-snapshot-race`](https://github.com/upamanyus/etcd/tree/fix/etcd-alarm-store-snapshot-race), off `main` (7ff040cb8). On `main`, `go test -race ./integration/ -run 'TestV3AlarmsDuringSnapshotInstall$'` (from `tests/`) fails as above, in 10 runs of 10. Without `-race` it passes.

### Anything else we need to know?

Found while formally verifying etcd. Written with the assistance of generative AI; I reproduced the bug and reviewed the report.

### Etcd version (please run commands below)

<details>

`main` (7ff040cb8), go1.27.2 linux/amd64; the integration test only, no binaries.

</details>

### Etcd configuration (command line flags or environment variables)

<details>

The test's cluster: three members, `SnapshotCount: 10`, `SnapshotCatchUpEntries: 5`.

</details>
