# etcd-alarm-store-snapshot-race

## Security classification

Not a security report: a data race on a pointer field whose effect, in practice, is that `Status` or a health
check reads the alarms of the old store for a moment. No crash, data loss or auth bypass found; no client
request controls it (it needs a member to apply a leader's snapshot).

## Candidate

- **Finding**: `issues/etcd-alarm-store-snapshot-race.md`
- **Target**: etcd-io/etcd, `main`. `restoreAlarms` has replaced the field unsynchronized since the alarm store was
  added; release branches likely have it too (not checked).
- **Branch**: `fix/etcd-alarm-store-snapshot-race` in `~/etcd-fixes/etcd-alarm-store-snapshot-race`, two commits:
  b2810d37a (`tests/integration: test Status during a snapshot install`) adds the test, which fails there under
  `-race`; 17a1a9c98 (`etcdserver: recover the alarm store in place on snapshot`) is the fix. Not pushed.
- **Base**: upstream `main` 7ff040cb84c9944d0c38a9f0dc9f12ed9c58223b (2026-10-20); `restoreAlarms`, `Alarms` and
  `applySnapshot` are as the finding describes them at the fork pin.
- **State**: draft
- **Upstream issue**: —
- **PR**: —

## Duplicates checked (2026-10-21)

Five searches on etcd-io/etcd (issues and PRs each): `alarmStore race`, `restoreAlarms`, `data race applySnapshot`,
`race Alarms snapshot`, `alarm store race`. No duplicate, no open PR. Related, different: #10871/#10874 (closed:
`s.be` read outside `bemu` in `applySnapshot`), #22608/#22609 (closed, merged at the base: mvcc `Hash` racing with
`Restore`, the same class in mvcc), #21873 (closed: `monitorKVHash` reading `s.be` without `bemu`), #13873/#13875
(closed: backend access race in tests).

## Verification (go1.27.2 linux/amd64)

`TestV3AlarmsDuringSnapshotInstall` (in `tests/integration/v3_alarm_test.go`, after `TestV3AlarmDeactivate`) is the
issue's example: three members, `SnapshotCount: 10`, `SnapshotCatchUpEntries: 5`; a follower is partitioned, the
leader takes 20 puts, eight goroutines call `Status` on the follower while the partition heals; a linearizable
`Get` through the follower waits until it has caught up, and the test checks that its backend changed (it applied
a snapshot). The race detector fails the test.

- At the tests commit b2810d37a (`cd tests; go test -race -c ./integration/`, then the binary with
  `-test.run 'TestV3AlarmsDuringSnapshotInstall$' -test.count=1`, one process per run, since the detector reports a
  given race once per process): fails 10 of 10, each with one `WARNING: DATA RACE`, write in `restoreAlarms`
  (`server.go:2399`, from `applySnapshot` `:1102`) against the read in `Alarms` (`:2426`, from
  `maintenanceServer.Status`). With the earlier 40-put version, 10 of 11 (one run caught no race).
- At the base by `go test -overlay` (the base's `server.go` and `alarms.go` over the fix commit): without `-race`
  the test passes 3 of 3 (the scenario runs, the follower applies a snapshot); with `-race` it fails 3 of 3.
- At the fix commit 17a1a9c98: the same, 15 of 15 pass (no race); in `server/`, `go test -race ./etcdserver/...
  ./storage/...` ok; `go build ./...` ok; `go vet ./etcdserver/ ./etcdserver/api/v3alarm/` clean; `gofmt -l` empty.
- At the fix commit, `cd tests; go test -race ./integration/ -run
  'Alarm|Quota|Snapshot|Maintenance|Status|Restore|Partition|Health' -count=1`: ok (47 s); `go test
  ./integration/ -count=1 -timeout 50m`: ok (464 s).
- Merges cleanly (`git merge-tree --write-tree`) with the sibling branches `fix/etcd-quota-stale-backend-after-snapshot`,
  `fix/etcd-auth-snapshot-closed-backend-panic` and `fix/etcd-merged-snapshot-stale-term`, which also touch
  `applySnapshot` or `v3_alarm_test.go`.

Not run: `tests/e2e`, `make verify` (golangci-lint; revive's `exported` rule is disabled, so the undocumented
`Recover` matches `Activate`/`Get`). The `/health` and `/readyz` readers (`etcdhttp/health.go:186`, `:422`) race the
same way by code reading; only the `Status` path was run.

## Why the test shows the bug and not a misuse

Every step is ordinary operation: a partitioned follower catching up by the leader's snapshot (the integration
framework's `InjectPartition`/`RecoverPartition`, as `TestV3WatchRestoreSnapshotUnsync` does) while clients call
the maintenance `Status` RPC, which monitoring tools do periodically. The expectation is Go's memory model: a field
written on the apply goroutine and read on gRPC goroutines needs synchronization; etcd's tests run with `-race`.

## Why the fix works

At the base, `applySnapshot` calls `restoreAlarms`, which builds a new `AlarmStore` from the new backend and assigns
`s.alarmStore` with no lock, after `bemu` is released; `Alarms()` (Status, `/health`, `/readyz`) loads the field with
no lock. With the fix, `applySnapshot` calls `s.alarmStore.Recover(...)`, which, under the store's own mutex (the one
`Get`, `Activate` and `Deactivate` already take), points the store at the new backend, clears the alarm map and
reloads it (`restore`, as `NewAlarmStore` does). `s.alarmStore` is then written once, in `NewServer`, before any
reader starts, so the field needs no synchronization, and readers see the alarms of before or after the snapshot.
The uber applier keeps the same pointer, which stays valid; it is rebuilt at the end of `applySnapshot` as before,
which recomputes the alarm-based appliers from the recovered alarms.

The two unit tests that build a partial `EtcdServer` and apply a snapshot (`TestSnapshotOrdering`,
`TestConcurrentApplyAndSnapshotV3`) relied on `restoreAlarms` creating the store; the fix commit gives them one,
as the second already does for the auth store.

## If a reviewer asks

Candidate fixes, at the layer of the alarm store and of the server:

- **Recover in place (chosen)**: `AlarmStore.Recover(be)`, called from `applySnapshot`. Every other store
  `applySnapshot` updates is the same object recovered in place: `lessor.Recover` (resets its maps and reloads
  under `le.mu`, the closest model; `Recover` mirrors it), `kv.Restore` (under `s.mu`), `authStore.Recover`,
  `cluster.SetBackend` + `cluster.Recover`. The alarm store was the only one replaced. It already has a mutex
  guarding `types` and `be`, so no new synchronization is added, and readers need no change. Nine lines plus one.
  `Recover` holds `a.mu` across `restore`'s `ForceCommit`, as `lessor.Recover` holds `le.mu` across its commit;
  lock order is the same as `Activate`'s (`a.mu`, then the batch transaction's lock), so no new deadlock.
  `restoreAlarms` stays, used only by `NewServer`; removing it and inlining `NewAlarmStore` there is a cosmetic
  follow-up kept out of this change.
- **`atomic.Pointer[v3alarm.AlarmStore]`** (the finding's first idea): `restoreAlarms` stores, `Alarms`,
  `NewUberApplier` and `apply` load. Correct, but it changes the field's type and four use sites, and no other
  store in `EtcdServer` is held that way; and it keeps replacing the object, so the uber applier and any reader
  holding the old store keep a store on the old, closed backend.
- **Under `bemu`**: assign inside `applySnapshot`'s `bemu` critical section and read under `bemu.RLock()` in
  `Alarms`. Couples the alarms to the backend lock, and would hold `bemu` (which every `s.Backend()` caller
  takes) across `NewAlarmStore`'s `ForceCommit` (an fsync), or need the store built before taking it, reordering
  `applySnapshot`.
- **A new mutex in `EtcdServer`** for the field: more code than the store's existing mutex, for the same effect.
- **Nil guard instead of the test change** (`if s.alarmStore != nil`, as for `s.lessor`/`s.authStore`): a server
  always has an alarm store after `NewServer`, so the guard would exist only for the two unit tests; giving them a
  store is cleaner.

Sibling: `issues/etcd-auth-snapshot-closed-backend-panic.md` notes the same unsynchronized pattern for the auth
store's `as.be` (written by `authStore.Recover`, read by permission checks); that is its own candidate and is not
changed here.

## Commit messages to rewrite

- `tests/integration: test Status during a snapshot install` (no body)
- `etcdserver: recover the alarm store in place on snapshot`, body: "Replacing the alarm store when applying a
  snapshot raced with the readers of the alarms on other goroutines."

## Push (when the user approves)

`git -C ~/etcd-fixes/etcd-alarm-store-snapshot-race push origin fix/etcd-alarm-store-snapshot-race`; then check the
issue's test link (`v3_alarm_test.go#L161-L202`) on GitHub.
