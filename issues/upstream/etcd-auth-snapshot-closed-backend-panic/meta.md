# etcd-auth-snapshot-closed-backend-panic

## Security classification: for the user to decide before anything is public

Decision pending (the user's). A public filing would expose that, with auth enabled, any authenticated user's
serializable read (and, by code reading, a watch, a lease keep-alive, an `Authenticate` attempt or a maintenance
request) can crash a member while it restores a snapshot from the leader.

## Candidate

- **Finding**: `issues/etcd-auth-snapshot-closed-backend-panic.md`
- **Target**: etcd-io/etcd, `main`
- **Branch**: `fix/etcd-auth-snapshot-closed-backend-panic` in `~/etcd-fixes/etcd-auth-snapshot-closed-backend-panic`,
  two commits (signed off, no trailers): 106cb7f10 (`tests/integration: test permission checks during snapshot
  restore`) adds the test; 2680ccf2b (`server: close the old backend after the auth store moves off it`) is the
  fix. Not pushed. (Before the 2026-10-21 review pass: e38927558 and 4c96cac84, off 6782f5229.)
- **Base**: upstream `main` bf9cadf044f0531036a61c9b6dbeba8aef2a3b30 (2026-10-21); `applySnapshot` and the auth
  store are unchanged since 6782f5229 and as the finding describes at the fork pin 8a24be2a3.
- **State**: draft (security decision pending, above)
- **Upstream issue**: —
- **PR**: —

## Duplicates checked (2026-10-19, rechecked 2026-10-21)

Five searches on 2026-10-19 (`applySnapshot oldbe.Close`; `auth snapshot nil pointer panic`; `isOpPermitted panic`;
`UnsafeRange nil pointer Bucket`; `closing old backend panic`). No issue or PR about the auth store reading the
backend `applySnapshot` is closing; no open PR fixes it. Same mechanism (a nil read transaction of a closed backend),
other triggers: #22189 (open: `Maintenance/Status` during shutdown reads the closed backend) with its fix #22190
(open, not merged; changes `StorageVersion` only, does not touch this path); #17223 (closed: `UnsafeRange` at
shutdown); #14256 (closed: same stack from watch at shutdown, 3.4). Same class: #21873 (closed, not merged:
`monitorKVHash` across the swap). Different: #13883 (closed: `Recover` did not refresh caches, fixed by #13920),
#13954 (closed: `rangePermCache` mutex), #17265, #15793 (closed: startup nil derefs).

2026-10-21, issues and PRs updated since 2026-10-19 (`applySnapshot`, `snapshot panic auth`, `authStore Recover`,
`closed backend`, `oldbe`, `backend Close race`, `isOpPermitted`): only #22608 (issue, open) and #22609 (PR,
merged at the base, afd94a12c): mvcc's `Hash` raced with `Restore` replacing the store's backend; the fix holds the
store's lock across the use of the backend, as this fix does for the auth store. Not a duplicate.

## Verification (go1.27.3 linux/amd64)

`TestV3AuthRangePermittedDuringSnapshotRestore` (`tests/integration/v3_auth_test.go`, lines 673-718, after the
other auth tests, with their `authSetupRoot`): 3 members, `SnapshotCount: 10`, `SnapshotCatchUpEntries: 5` (as
`TestV3WatchRestoreSnapshotUnsync`); auth enabled with `root`; a follower partitioned (`InjectPartition`) while 20
puts go through the leader; 4 goroutines call `follower.Server.AuthStore().IsRangePermitted` for `root` (the check
of a serializable `Range`) in a loop, and each check must return nil; the partition heals; a linearizable `Get` on
the follower (which returns only after the follower has applied the snapshot) must succeed; setup check that the
follower's backend changed (`require.NotSame`). About 1.4 s per run.

The review pass replaced the earlier test (32 goroutines sending serializable `Get`s through gRPC), which failed in
18 of 20 runs on ext4 and 3 of 20 on tmpfs at the base: calling the check directly, as
`TestV3AlarmsDuringSnapshotInstall` calls `Server.Alarms()`, fails more reliably and asserts each answer. The gRPC
version is quoted in the issue: at the base, 19 of 20 runs on ext4 panicked from `kvServer.Range`.

Each count is one process per run (`cd tests; go test [-race] -c ./integration/`, then the binary with `-test.run
'^TestV3AuthRangePermittedDuringSnapshotRestore$' -test.count=1`, `TMPDIR` on ext4 or tmpfs). "Base (overlay)" is
the fix commit with `-overlay` replacing both files the fix changes (`server/auth/store.go`,
`server/etcdserver/server.go`) by the base's; "reorder only" overlays `store.go` only, "lock only" `server.go` only.

| code | TMPDIR | flags | failed | how |
|---|---|---|---|---|
| tests commit 106cb7f10 | ext4 | | 10/10 | nil-pointer panic in `isOpPermitted` |
| tests commit 106cb7f10 | ext4 | `-race` | 5/5 | same panic |
| base (overlay) | ext4 | | 20/20 | same panic |
| base (overlay) | tmpfs | | 12/20 | same panic |
| base (overlay) | ext4 | `-race` | 20/20 | same panic (8 also report the `as.be` race) |
| base (overlay) | tmpfs | `-race` | 20/20 | same panic (9 also report the `as.be` race) |
| base, gRPC test (e38927558's) | ext4 | | 19/20 | same panic, from `kvServer.Range` |
| reorder only | ext4 | `-race` | 10/10 | data race: `Recover` writes `as.be`, `isOpPermitted` reads it; no panic |
| reorder only | tmpfs | | 0/20 | |
| lock only | ext4 | | 10/10 | nil-pointer panic |
| fix 2680ccf2b | ext4 | | 0/20 | |
| fix | tmpfs | | 0/20 | |
| fix | ext4 | `-race` | 0/20 | |
| fix | tmpfs | `-race` | 0/20 | |

The window is the old backend's close running while `restoreAlarms` (an fsync) runs; on tmpfs the fsync is free and
the close often starts only after `Recover`, so without `-race` the test fails about half the runs there; on disk,
and under `-race` (as upstream CI runs the integration tests, `scripts/test.sh`), every run. With the reorder alone,
the test fails under `-race`, which is why the fix includes the lock.

At the fix: `go test ./auth/... ./etcdserver/... ./storage/schema/... -count=1` (in `server/`) ok;
`go test -race ./auth/ ./etcdserver/` ok; in `tests/` (`TMPDIR` on ext4): `go test -race ./integration/ -run
'Auth|Snapshot|Restore'` ok; `go test -race ./integration/clientv3/watch/ ./integration/clientv3/
./integration/clientv3/snapshot/ -run 'Restore|Snapshot|Auth|Maintenance'` ok; `gofmt -l` empty on the changed
packages; `go vet ./auth/ ./etcdserver/` (server) and `./integration/` (tests) clean.

`check.py`: no FAIL; WARNs kept: the added comments (each says why: the order the close needs, and what `beMu`
guards against), the issue at 283 words of prose and the PR at 118 (aims 250 and 90), since the PR has two changes
to explain (the reorder and the lock) and the issue quotes both the direct and the gRPC variants.

Not run: the whole `tests/integration` suite, `tests/e2e`, `make verify` (golangci-lint), release branches.

## The sibling candidates

`git merge-tree --write-tree` of this branch with each of `fix/etcd-alarm-store-snapshot-race` (d396a0fc7, which
changes the alarm-store line of the same `applySnapshot`), `fix/etcd-merged-snapshot-stale-term` (f81ca1509) and
`fix/etcd-quota-stale-backend-after-snapshot` (563ae7f6c): clean, and the merge of all four is clean. In the merge
of all four, `server/` builds, `go vet` of `auth`, `etcdserver`, `v3rpc` and `tests/integration` is clean,
`go test -race ./etcdserver/ ./auth/` passes, and the three branches' integration tests
(`TestV3AuthRangePermittedDuringSnapshotRestore`, `TestV3AlarmsDuringSnapshotInstall`,
`TestV3StorageQuotaAfterSnapshot`) pass under `-race`, 3 runs each. No conflict note in the PR.

## Why the test shows the bug and not a misuse

Every step is ordinary operation: a follower partitioned and healed (the harness's `InjectPartition` /
`RecoverPartition`), puts through the leader, the snapshot-catch-up settings other integration tests use. The test
calls the follower's `IsRangePermitted` with the `AuthInfo` a client authenticated as `root` gets, as a serializable
`Range` does on a gRPC goroutine (`doSerialize`); the gRPC version shows the same panic from `kvServer.Range`.
Nothing documents that a member may crash on a client request while it catches up; the expectation is that every
check answers (here, `nil`) and the member keeps serving (the final linearizable `Get`).

## Why the fix works

At the base, `applySnapshot` sets `s.be = newbe`, starts `go oldbe.Close()`, runs `restoreAlarms`, then
`authStore.Recover(newbe)`. The close runs `CommitAndStop`, which takes the read transaction's write lock (waiting
for read-locked readers), resets it (`tx = nil`) and opens no new one. A permission check that loads `as.be` (still
old) and locks a read transaction after that reset ranges over a nil `*bolt.Tx` and panics; etcd's gRPC server has
no panic recovery, so the process exits.

With the fix:
- `server.go`: the `go oldbe.Close()` block (unchanged) moves from right after the swap to right after
  `s.cluster.SetBackend(...)`, i.e. after `restoreAlarms`, `authStore.Recover` and the membership store's switch.
- `auth/store.go`: `Recover` assigns `as.be` under a new `beMu` (write lock); the three checks that run outside the
  apply loop (`CheckPassword`, `isOpPermitted`, `IsAdminPermitted`) get their read transaction from a new
  `lockedReadTx`, which, under `beMu.RLock`, calls `as.be.ReadTx()` and `tx.RLock()`.

So a check either locks its transaction before `Recover` replaces `as.be` (then `Close`, which starts after
`Recover` returns, waits in `CommitAndStop` for that check's `RUnlock`), or loads the new backend. No check can lock
a transaction of the old backend after its reset. The `as.be` race goes away for those checks; the other readers of
`as.be` (user and role admin including `UserGet`/`RoleGet`/`UserList`/`RoleList`, `Authenticate`,
`AuthEnable`/`AuthDisable`, `HasRole`) run on the apply loop, the same goroutine as `Recover`. Lock order is `beMu`
then the read transaction's lock; `Recover` holds `beMu` only for the assignment; the batch loop takes the read
transaction's write lock without `beMu`; nothing holds a read transaction's lock while taking `beMu`.

Other readers of the old backend after the swap: the stores the fix does not touch move to `newbe` before the close
(lessor and mvcc before the swap, under `bemu`; alarms, auth and membership now before the close). A read that
started on the old backend before the swap is safe across the close: a read-locked `ReadTx` blocks `CommitAndStop`
until `RUnlock`, a `ConcurrentReadTx` keeps its own `*bolt.Tx` (the reset rolls it back only after the read's
`txWg` is done), and bolt's `Close` waits for open read transactions.

## If a reviewer asks

Candidate layers and fixes:
- Reorder only (the finding's first patch): smallest, and the test passes without `-race`; but `as.be` stays an
  unsynchronized field written by `Recover` and read by gRPC goroutines: the race detector reports it in this test
  (10/10 runs, above), and a check that loaded the old `as.be` just before `Recover` and locks its transaction after
  the close started can still panic (tiny window, not reproduced). The race is not a separate bug: it is the same
  hand-off of the auth store's backend, and without the lock the reorder does not close the window.
- Lock only: does not help; the checks then read the old backend, correctly synchronized, while it is being closed
  (10/10 panics, above).
- `atomic.Pointer` for `be`: removes the race but not the remaining window (the load and the `RLock` are still
  separate), and changes every use of `as.be`.
- The auth store reading through the server's current backend (`s.be` under `bemu`) instead of a field of its own:
  the auth package does not know the server; it would mean an accessor in `AuthBackend` and `bemu` on every check,
  a larger change for the same ordering (the close would still have to wait for checks that hold the old backend).
- The backend refusing reads after close (`baseReadTx` checks `tx == nil`): a change in the storage layer for every
  caller; an empty result would make the check deny permission (`ErrPermissionDenied` for a valid user) instead of
  answering from the new backend, and the `as.be` race remains.
- Holding `s.bemu` across the restore: the checks do not go through `s.bemu`; the auth store has its own field.

The chosen fix is the order change plus the auth store's own lock: the defect is that `applySnapshot` closes a
backend that a store still reads, and that `Recover` hands the auth store a new backend without synchronizing with
its readers; mvcc's #22609 (merged at the base) fixed the same hand-off in `store.hash` the same way.

- Cost: one uncontended `RWMutex` read lock per permission check.
- Other holders of the old backend after the swap: the maintenance `Snapshot` RPC taking `Backend()` twice has a
  narrower window of the same class; found by reading the code, not reproduced, recorded in the finding, not in
  this PR (`store.hash` behind the `Hash` RPC was fixed upstream by #22609).
- Backports: not checked or run on release branches.

## Applying the same fix elsewhere

The fix commit's diff is self-contained (two files, no API change): `server/etcdserver/server.go` moves the
`go func() { ... oldbe.Close() ... }()` block, with its comment plus two new lines, after
`s.cluster.SetBackend(schema.NewMembershipBackend(lg, newbe))`; `server/auth/store.go` adds `beMu sync.RWMutex` to
`authStore`, wraps `as.be = be` in `Recover` with `beMu.Lock`/`Unlock`, adds `lockedReadTx`, and replaces
`tx := as.be.ReadTx(); tx.RLock()` by `tx := as.lockedReadTx()` in `CheckPassword`, `isOpPermitted` and
`IsAdminPermitted`.
