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
  9cf3ac84b (`tests/integration: test reading alarms while applying a snapshot`) adds the test, which fails there
  under `-race`; d396a0fc7 (`etcdserver: fix data race on the alarm store when applying a snapshot`) is the fix.
  Not pushed. (Before the 2026-10-21 review pass: b2810d37a and 17a1a9c98.)
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

`TestV3AlarmsDuringSnapshotInstall` (in `tests/integration/v3_alarm_test.go`, lines 161-199, after
`TestV3AlarmDeactivate`) is the issue's example: three members, `SnapshotCount: 10`, `SnapshotCatchUpEntries: 5`; a
follower is partitioned, the leader takes 20 puts, one goroutine calls `follower.Server.Alarms()` in a loop while
the partition heals; a linearizable `Get` through the follower waits until it has caught up, and the test checks
that its backend changed (it applied a snapshot). The race detector is the assertion. About 0.4 s per run.

Each count below is one process per run (`cd tests; go test -race -c ./integration/`, then the binary with
`-test.run 'TestV3AlarmsDuringSnapshotInstall$' -test.count=1`), since the detector reports a given race once per
process.

- At the tests commit 9cf3ac84b (the base plus the test): with `-race`, fails 20 of 20 (2026-10-21), each run with
  two or three `WARNING: DATA RACE`: the write of the field in `restoreAlarms` (`server.go:2399`, from
  `applySnapshot` `:1102`) against the read in `Alarms` (`:2426`), and `Get` reading the new store's mutex and map
  against their initialization in `NewAlarmStore` (`alarms.go:48`), i.e. a reader seeing a partly initialized
  store. Without `-race`, passes 5 of 5 (the scenario runs, the follower applies a snapshot).
- The earlier version of the test, with eight goroutines calling `Status` on the follower instead of
  `Server.Alarms()`, failed only 15 of 20 at the base (also 15 of 20 with 16 and with 32 goroutines): `Status`
  takes locks the apply goroutine also takes while installing the snapshot (the backend's read transaction, which
  `NewAlarmStore`'s commit locks; the auth store's and the cluster's), which order most of its reads of the field
  with the write, so the detector sees an unordered pair only when a read falls in the commit's window. Reading the
  alarms directly has no such edges, so it is the reliable and smaller reproduction; the issue keeps the `Status`
  run as the user-visible case.
- At the fix commit d396a0fc7: the test passes 20 of 20 with `-race` (no race); in `server/`, `go test -race
  ./etcdserver/... ./storage/...` ok; `go build ./...` ok; `go vet ./etcdserver/ ./etcdserver/api/v3alarm/` and
  `go vet ./integration/` (in `tests/`) clean; `gofmt -l` empty; `cd tests; go test -race ./integration/ -run
  'Alarm|Quota|Snapshot|Maintenance|Status|Restore|Partition|Health' -count=1`: ok (43 s).
- Before the review pass (same fix but the comment), `go test ./integration/ -count=1 -timeout 50m`: ok (464 s);
  not rerun.
- Merges cleanly (`git merge-tree --write-tree`, checked before the review pass) with the sibling branches
  `fix/etcd-quota-stale-backend-after-snapshot`, `fix/etcd-auth-snapshot-closed-backend-panic` and
  `fix/etcd-merged-snapshot-stale-term`, which also touch `applySnapshot` or `v3_alarm_test.go`.

CI: etcd's integration jobs (`make test-integration`, `PASSES="integration" ./scripts/test.sh`) run with `--race` on
amd64 and arm64 (`scripts/test.sh` sets `RACE="--race"` for those `GOARCH`es unless `RACE` is set), so the test
fails there at the base; on other architectures it runs without the detector and passes.

Not run: `tests/e2e`, `make verify` (golangci-lint; revive's `exported` rule is disabled, so the undocumented
`Recover` matches `Activate`/`Get`). The `/health` and `/readyz` readers (`etcdhttp/health.go:186`, `:422`) race the
same way by code reading; the `Status` path was run (above).

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

`git -C ~/etcd-fixes/etcd-alarm-store-snapshot-race push origin fix/etcd-alarm-store-snapshot-race`; then check the
issue's test link (`v3_alarm_test.go#L161-L199`) on GitHub.
