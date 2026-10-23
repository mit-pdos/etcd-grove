# etcd-alarm-store-snapshot-race

## Security classification

Not a security report: a data race on a pointer field whose effect, in practice, is that `Status` or a health
check reads the alarms of the old store for a moment. No crash, data loss or auth bypass found; no client
request controls it (it needs a member to apply a leader's snapshot).

## Candidate

- **Finding**: `issues/etcd-alarm-store-snapshot-race.md`
- **Target**: etcd-io/etcd, `main`. `restoreAlarms` has replaced the field unsynchronized since the alarm store was
  added; release branches likely have it too (not checked).
- **Branch**: `fix/etcd-alarm-store-snapshot-race` in `~/etcd-fixes/etcd-alarm-store-snapshot-race`, two commits
  (rebuilt 2026-10-23 on the new base, both commits cherry-picked unchanged): a89993c86
  (`tests/integration: test reading alarms while applying a snapshot`) adds the test, which fails there under
  `-race`; 7569d2bbd (`etcdserver: fix data race on the alarm store when applying a snapshot`) is the fix. Not
  pushed (`git ls-remote origin` has no `fix/etcd-alarm-store-snapshot-race`). The previous head, on 7ff040cb8, is
  kept as `backup/etcd-alarm-store-snapshot-race-v1` (d396a0fc7; before the 2026-10-21 review pass: b2810d37a and
  17a1a9c98).
- **Base**: upstream `main` 3aaab3479b6c4f5fe1b2b8f33437093c2caae88a (2026-10-22). The 22 commits since 7ff040cb8
  touch none of `server/etcdserver/`, `tests/integration/v3_alarm_test.go` or raft's version (v3.7.0); `restoreAlarms`,
  `Alarms` and `applySnapshot` are as the finding describes them, at the same lines.
- **State**: draft
- **Upstream issue**: —
- **PR**: —

## Duplicates checked (2026-10-21, rechecked 2026-10-23)

2026-10-23: `alarmStore race`, `restoreAlarms`, `"data race" applySnapshot alarm`, `Alarms Status race snapshot`,
`"data race" alarm` and `race` updated since 2026-10-20: no duplicate, no open PR. New since the first check: only the
backports of #22609 (#22636, #22637, #22640, closed 2026-10-22), unrelated to the alarm store.

2026-10-21: five searches on etcd-io/etcd (issues and PRs each): `alarmStore race`, `restoreAlarms`, `data race applySnapshot`,
`race Alarms snapshot`, `alarm store race`. No duplicate, no open PR. Related, different: #10871/#10874 (closed:
`s.be` read outside `bemu` in `applySnapshot`), #22608/#22609 (closed, merged at the base: mvcc `Hash` racing with
`Restore`, the same class in mvcc), #21873 (closed: `monitorKVHash` reading `s.be` without `bemu`), #13873/#13875
(closed: backend access race in tests).

## Verification

Rerun 2026-10-23 at the rebuilt branch (go1.27.3 linux/amd64). Each count is one process per run (`cd tests; go
test -race -c ./integration/` at each commit, then the binary with `-test.run 'TestV3AlarmsDuringSnapshotInstall$'
-test.count=1`), since the detector reports a given race once per process.

- At the tests commit a89993c86: with `-race`, fails 20 of 20, each run with two or three `WARNING: DATA RACE`: the
  write of the field in `restoreAlarms` (`server.go:2399`, from `applySnapshot` `:1102`) against the read in
  `Alarms` (`:2426`, from the test's goroutine, `v3_alarm_test.go:190`), and `Get` reading the new store's mutex and
  map against their initialization in `NewAlarmStore`, i.e. a reader seeing a partly initialized store. The output
  in `issue.md` is from the first of these runs. Without `-race`: `go test ./integration/ -run
  'TestV3AlarmsDuringSnapshotInstall$' -count=5` ok (the scenario runs, the follower applies a snapshot).
- The `Status` variant (the finding's `issues/etcd-alarm-store-snapshot-race/repro_test.go`, eight goroutines
  calling `Status` on the follower, 40 puts, built into the tests commit under another name): fails 20 of 20 at the
  base, each with a report whose read is `Alarms` from `maintenanceServer.Status` (`maintenance.go:301`). (At
  7ff040cb8 on 2026-10-21 it failed 15 of 20: `Status` takes locks the apply goroutine also takes, which order most
  of its reads with the write; the rate varies by machine load. Reading the alarms directly has no such edges, so
  the branch's test is the reliable and smaller reproduction; the issue keeps `Status` as the user-visible case.)
- At the fix commit 7569d2bbd: the test passes 20 of 20 with `-race` (no race); in `server/`, `go test -race
  ./etcdserver/... ./storage/...` ok; `go vet ./etcdserver/ ./etcdserver/api/v3alarm/` and `go vet ./integration/`
  (in `tests/`) clean; `gofmt -l` of the changed files empty; `cd tests; go test -race ./integration/ -run
  'Alarm|Quota|Snapshot|Maintenance|Status|Restore|Partition|Health' -count=1`: ok (46 s).
- 2026-10-21, at 7ff040cb8 (same diff): the test failed 20 of 20 at the tests commit and passed 20 of 20 at the fix;
  `go test ./integration/ -count=1 -timeout 50m`: ok (464 s); not rerun on the new base.
- Merges cleanly (`git merge-tree --write-tree`, rechecked 2026-10-23 with the rebuilt branch) with the sibling
  branches `fix/etcd-quota-stale-backend-after-snapshot`, `fix/etcd-auth-snapshot-closed-backend-panic` and
  `fix/etcd-merged-snapshot-stale-term`, which also touch `applySnapshot` or `v3_alarm_test.go`, and with
  `fix/etcd-compact-past-raft-applied`; no conflict.

CI: etcd's integration jobs (`make test-integration`, `PASSES="integration" ./scripts/test.sh`) run with `--race` on
amd64 and arm64 (`scripts/test.sh` sets `RACE="--race"` for those `GOARCH`es unless `RACE` is set), so the test
fails there at the base; on other architectures it runs without the detector and passes.

Not run: `tests/e2e`, `make verify` (golangci-lint; revive's `exported` rule is disabled, so the undocumented
`Recover` matches `Activate`/`Get`). The `/health` and `/readyz` readers (`etcdhttp/health.go:186`, `:422`) race the
same way by code reading; the `Status` path was run (above).

## Review (2026-10-23, after the rebuild)

By hand, as a maintainer, at the new base: `s.alarmStore` is now written only by `restoreAlarms` from `NewServer`,
before any reader starts; its readers (`Alarms`, `apply`'s `NOSPACE` check, `NewUberApplier`) keep the same
pointer. Between `s.be = newbe` and `Recover`, the store still points at the old backend, which is being closed
asynchronously; nothing writes alarms then, since alarm requests are applied on the apply goroutine, which is in
`applySnapshot`, and `Get` reads only the map. `Recover` uses `applySnapshot`'s `lg` where `restoreAlarms` used
`s.lg`; both are the server's logger. No comment still claims the store is replaced. No new bug found; the fix is
unchanged. `check.py` passes; its one WARN, on the reworded comment before the uber applier's rebuild, is kept:
the line replaces an existing comment that named the alarm store as replaced.

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

The comment before the uber applier's rebuild at the end of `applySnapshot` said "implementations like alarmsStore
changed"; the fix commit rewords it ("the backend and the alarms changed"), since the alarm store is now the same
object.

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
  `Recover` returns `restore`'s error, as `NewAlarmStore` does, and `applySnapshot` panics on it as before (the
  lessor and auth store's `Recover` cannot fail). Readers see the clear and the reload as one step, since `Get`
  takes the same mutex; a new backend without the alarm bucket is handled by `restore`'s `CreateAlarmBucket`, as at
  startup. `restoreAlarms` stays, used only by `NewServer`; removing it and inlining `NewAlarmStore` there is a
  cosmetic follow-up kept out of this change.
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

- `tests/integration: test reading alarms while applying a snapshot` (no body)
- `etcdserver: fix data race on the alarm store when applying a snapshot`, body: "Recover the alarm store in place,
  as the lessor is, instead of replacing it while other goroutines read it."

## Push (when the user approves)

`git -C ~/etcd-fixes/etcd-alarm-store-snapshot-race push origin fix/etcd-alarm-store-snapshot-race` (never pushed,
so no `--force-with-lease`); then check the issue's test link (`v3_alarm_test.go#L161-L199`) on GitHub.
