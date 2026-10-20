# etcd-auth-snapshot-closed-backend-panic

## Security classification: for the user to decide before anything is public

A client with ordinary access (any authenticated user's serializable `Get`; by code reading also a watch, a lease
keep-alive, `Authenticate` or a maintenance request) can crash a member while it restores a snapshot. The skill's
rule makes that a candidate security report, so nothing here is to be filed publicly until the user decides.

What etcd asks (`security/README.md` at the base): report a vulnerability privately through GitHub's Security
Vulnerability Reporting Form (`https://github.com/etcd-io/etcd/security/advisories/new`), not a public issue, when
it affects a supported release and is a security issue under `THREAT_MODEL.md`. The Product Security Committee
acknowledges within 5 working days and runs the Security Release Process; the disclosure date is negotiated with the
reporter (usually 1-3 weeks, the committee has the final say). Not to be reported there: findings clearly outside
the threat model.

What `THREAT_MODEL.md` says about this case (it points the other way): traffic that has passed client mTLS is
trusted input, and "crashes, memory exhaustion, or resource leaks triggered by malformed or high-volume requests
from an authenticated client are robustness defects, not vulnerabilities"; a report must show reachability by an
unauthenticated actor or an effect beyond the sender's privileges. Built-in RBAC is "an optional, secondary
control", disabled by default, and reports predicated on a non-default flag are hardening. Here the trigger needs
auth enabled, an mTLS-admitted client, and a member restoring a snapshot (it fell behind); by code reading (not
reproduced end to end), the request can be `Authenticate` with any user name and password, which reads the user
before comparing passwords, so an etcd user account is not needed, but transport access is. By the
threat model's letter that is a robustness defect, welcome as a normal issue and PR. The threat model also says
"not a vulnerability never means do not report", and that the committee decides.

Options: (a) file `issue.md` and the PR publicly, as a robustness defect under the threat model; (b) send the
report through the private form first and let the committee classify it. The drafts below are written for (a);
for (b) the same issue text fits the form.

## Candidate

- **Finding**: `issues/etcd-auth-snapshot-closed-backend-panic.md`
- **Target**: etcd-io/etcd, `main`
- **Branch**: `fix/etcd-auth-snapshot-closed-backend-panic` in `~/etcd-fixes/etcd-auth-snapshot-closed-backend-panic`,
  two commits (signed off, no trailers): e38927558 (`tests/integration: test reads during snapshot restore with
  auth`) adds the test; 4c96cac84 (`server: close the old backend after the auth store moves off it`) is the fix.
  Not pushed.
- **Base**: upstream `main` 6782f5229b8a6dbc5f6d421107fd70d66de98694 (2026-10-19); `applySnapshot` and the auth
  store are as the finding describes at the fork pin 8a24be2a3.
- **State**: draft (security decision pending, above)
- **Upstream issue**: —
- **PR**: —

## Duplicates checked (2026-10-19)

Five searches (`applySnapshot oldbe.Close`; `auth snapshot nil pointer panic`; `isOpPermitted panic`;
`UnsafeRange nil pointer Bucket`; `closing old backend panic`). No issue or PR about the auth store reading the
backend `applySnapshot` is closing; no open PR fixes it. Same mechanism (a nil read transaction of a closed backend),
other triggers: #22189 (open: `Maintenance/Status` during shutdown reads the closed backend) with its fix #22190
(open, not merged; changes `StorageVersion` only, does not touch this path); #17223 (closed: `UnsafeRange` at
shutdown); #14256 (closed: same stack from watch at shutdown, 3.4). Same class: #21873 (closed, not merged:
`monitorKVHash` across the swap). Different: #13883 (closed: `Recover` did not refresh caches, fixed by #13920),
#13954 (closed: `rangePermCache` mutex), #17265, #15793 (closed: startup nil derefs).

## Verification (go1.27.2 linux/amd64)

`TestV3AuthSerializableGetDuringSnapshotRestore` (`tests/integration/v3_auth_test.go`, after the other auth tests,
with their `authSetupRoot`): 3 members, `SnapshotCount: 10`, `SnapshotCatchUpEntries: 5` (as
`TestV3WatchRestoreSnapshotUnsync`); auth enabled with `root`; a follower partitioned (`InjectPartition`) while 40
puts go through the leader; 32 goroutines send serializable `Get`s as `root` to the follower; the partition heals;
a linearizable `Get` on the follower (which returns only after the follower has applied the snapshot) must
succeed; setup check that the follower's backend changed (`require.NotSame`, so the race detector does not see a
deep comparison of the live backend).

Run from `tests/`: `go test [-race] ./integration -run TestV3AuthSerializableGetDuringSnapshotRestore -count=1`, N
times (`TMPDIR` on ext4 or the default `/tmp`, which is tmpfs here). Base runs are at the tests commit, or with
`-overlay` replacing both files the fix changes by the base's.

| code | TMPDIR | flags | failed | how |
|---|---|---|---|---|
| base (overlay) | ext4 | | 10/10 | nil-pointer panic in `isOpPermitted` |
| base (overlay) | tmpfs | | 5/10 | same panic |
| tests commit e38927558 | ext4 | | 3/3 | same panic |
| tests commit e38927558 | tmpfs | | 2/5 | same panic |
| base (overlay) | ext4 | `-race` | 5/5 | panic (3 runs also report the `as.be` race) |
| reorder only (overlay of `store.go`) | ext4 | `-race` | 5/5 | data race `Recover` write / `isOpPermitted` read of `as.be`; no panic |
| lock only (overlay of `server.go`) | ext4 | | 10/10 | nil-pointer panic |
| reorder only (before the lock was added) | ext4 | | 0/10 | |
| reorder only (before the lock was added) | tmpfs | | 0/20 | |
| fix 4c96cac84 | ext4 | | 0/10 | |
| fix | tmpfs | | 0/10 | |
| fix | ext4 | `-race` | 0/10 | |
| fix | tmpfs | `-race` | 0/5 (one `-count=5` run) | |

The window is the old backend's close running while `restoreAlarms` (an fsync) runs; on tmpfs the fsync is free and
the window is short, so the test fails about half the runs there; on disk it fails every run. Upstream CI runs the
integration tests with `--race` (`scripts/test.sh`), which is why the fix includes the lock: with the reorder
alone, the new test fails under `-race`.

At the fix: `go test ./auth/... ./etcdserver/... ./storage/schema/... -count=1` (in `server/`) ok;
`go test -race ./auth/ ./etcdserver/` ok; `go test -race ./integration/ -run 'Auth|Snapshot|Restore'` (in
`tests/`) ok; `go test -race ./integration/clientv3/watch/ -run 'Restore|Snapshot|Auth'` ok; `go test -race
./integration/clientv3/ ./integration/clientv3/snapshot/ -run 'Restore|Snapshot|Auth|Maintenance'` ok; `go test -race
./integration/ -run TestV3Auth` ok at the final commit; `gofmt -l` empty on the
changed packages; `go vet ./auth/ ./etcdserver/` (server) and `./integration/` (tests) clean.
`git merge-tree --write-tree` with `fix/etcd-quota-stale-backend-after-snapshot` (the other snapshot-path
candidate): clean.

The issue is 278 words of prose and the PR 120 (check.py aims for 250 and 90): kept, since the PR has two changes
to explain (the reorder and the lock).

Not run: the whole `tests/integration` suite, `tests/e2e`, `make verify` (golangci-lint), release branches.

## Why the test shows the bug and not a misuse

Every step is ordinary operation: a follower partitioned and healed (the harness's `InjectPartition` /
`RecoverPartition`), puts through the leader, serializable reads by an authenticated user against the follower,
the snapshot-catch-up settings other integration tests use. Serializable reads are documented as served by the
local member without consensus. Nothing documents that a member may crash on a client request while it catches up;
the expectation is that every `Get` returns a response or an error and the member keeps serving (the final
linearizable `Get`).

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
`as.be` (user/role admin, `Authenticate`, `AuthEnable`/`AuthDisable`, `HasRole`) run on the apply loop, the same
goroutine as `Recover`. Lock order is `beMu` then the read transaction's lock; `Recover` holds `beMu` only for the
assignment, and nothing holds a read transaction's lock while taking `beMu`.

## If a reviewer asks

- Reorder only (the finding's first patch): smallest, and the test passes without `-race`; but `as.be` stays an
  unsynchronized field written by `Recover` and read by gRPC goroutines, the race detector reports it in this test
  (5/5 runs, above), and a check that loaded the old `as.be` just before `Recover` and locks its transaction after
  the close started can still panic (tiny window, not reproduced).
- Lock only: does not help; the checks then read the old backend, correctly synchronized, while it is being closed
  (10/10 panics, above).
- `atomic.Pointer` for `be`: removes the race but not the remaining window (the load and the `RLock` are still
  separate), and changes every use of `as.be`.
- The backend refusing reads after close (`baseReadTx` checks `tx == nil`): a change in the storage layer for every
  caller; an empty result would make the check deny permission (`ErrPermissionDenied` for a valid user) instead of
  answering from the new backend, and the `as.be` race remains.
- Holding `s.bemu` across the restore: the checks do not go through `s.bemu`; the auth store has its own field.
- Cost: one uncontended `RWMutex` read lock per permission check.
- Other holders of the old backend after the swap (`store.hash` behind the `Hash` RPC, the maintenance `Snapshot`
  RPC taking `Backend()` twice) have narrower windows of the same class; found by reading the code, not reproduced,
  recorded in the finding, not in this PR.
- Backports: not checked or run on release branches.

## Applying the same fix elsewhere

The fix commit's diff is self-contained (two files, no API change): `server/etcdserver/server.go` moves the
`go func() { ... oldbe.Close() ... }()` block, with its comment plus two new lines, after
`s.cluster.SetBackend(schema.NewMembershipBackend(lg, newbe))`; `server/auth/store.go` adds `beMu sync.RWMutex` to
`authStore`, wraps `as.be = be` in `Recover` with `beMu.Lock`/`Unlock`, adds `lockedReadTx`, and replaces
`tx := as.be.ReadTx(); tx.RLock()` by `tx := as.lockedReadTx()` in `CheckPassword`, `isOpPermitted` and
`IsAdminPermitted`.
