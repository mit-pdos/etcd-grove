---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/etcd#17223 issue closed: the same nil read tx (`UnsafeRange` on a closed backend), reached at shutdown; closed by #17757 and gRPC's GracefulStop draining handlers, which do not cover a snapshot install
  - etcd-io/etcd#21873 pr closed: the same class (a holder of `s.be` using it across applySnapshot's swap and close), for `monitorKVHash`; not merged
  - etcd-io/etcd#13883 issue closed: a different `authStore.Recover` bug (its caches were not refreshed), fixed by #13920
  - etcd-io/etcd#22189 issue open: the same nil read tx of a closed backend, from `Maintenance/Status` during shutdown; not this path
  - etcd-io/etcd#22190 pr open: the fix of #22189 (`StorageVersion` only); does not fix this
  - etcd-io/etcd#14256 issue closed: the same `Tx.Bucket` stack from watch at shutdown (3.4)
  - etcd-io/etcd#22608 issue closed: the same class in mvcc (`store.hash` racing with `Restore` replacing the backend); fixed by #22609
  - etcd-io/etcd#22609 pr merged: holds mvcc's `s.mu` across `Hash`'s use of the backend; does not touch the auth store
blocks-proof: yes
---

# server: a member with auth enabled panics on a permission check while it restores a snapshot from the leader

With auth enabled, a member that has fallen behind and is restoring a snapshot sent by the leader
crashes (nil-pointer panic) if a serializable read reaches it during the restore. Watch creation,
lease keep-alives, `Authenticate` and maintenance requests check permissions the same way.

**Expected:** a member should answer every request while it catches up by a snapshot, and keep
running; nothing documents that a client request may crash a member during a snapshot restore.

**Impact:** any cluster with auth enabled in which a member falls far enough behind to be sent a
snapshot (a partition, a slow or restarted member) while clients send it serializable reads,
watches or keep-alives. The member process exits; a restart recovers it. Reproduced on `main`; release
branches not checked.

**Reproduction:** `TestV3AuthRangePermittedDuringSnapshotRestore` in
[`issues/etcd-auth-snapshot-closed-backend-panic/snapshot_restore_auth_test.go`](etcd-auth-snapshot-closed-backend-panic/snapshot_restore_auth_test.go),
copied into `tests/integration` at etcd-io/etcd@1573d5941 (2026-10-28), go1.27.3 linux/amd64. A
3-member cluster (`SnapshotCount: 10`, `SnapshotCatchUpEntries: 5`, auth on with `root`); a
follower is partitioned while 20 puts go through the leader; 4 goroutines call the follower's
`IsRangePermitted` for `root` (the check a serializable `Range` makes); the partition heals:

```
$ go test ./integration -run '^TestV3AuthRangePermittedDuringSnapshotRestore$' -count=1
panic: runtime error: invalid memory address or nil pointer dereference [recovered, repanicked]
[signal SIGSEGV: segmentation violation code=0x1 addr=0x0 pc=0xc86d93]
go.etcd.io/bbolt.(*Tx).Bucket(...)
	go.etcd.io/bbolt@v1.5.0/tx.go:112
go.etcd.io/etcd/server/v3/storage/backend.(*baseReadTx).UnsafeRange(...)
	server/storage/backend/read_tx.go:103 +0x233
go.etcd.io/etcd/server/v3/storage/schema.unsafeGetUser(...)
	server/storage/schema/auth_users.go:57 +0x9d
go.etcd.io/etcd/server/v3/storage/schema.(*authReadTx).UnsafeGetUser(...)
	server/storage/schema/auth_users.go:53 +0x4d
go.etcd.io/etcd/server/v3/auth.(*authStore).isOpPermitted(...)
	server/auth/store.go:883 +0x4af
go.etcd.io/etcd/server/v3/auth.(*authStore).IsRangePermitted(...)
	server/auth/store.go:906 +0x4e
go.etcd.io/etcd/tests/v3/integration.TestV3AuthRangePermittedDuringSnapshotRestore.func1()
FAIL	go.etcd.io/etcd/tests/v3/integration	0.350s
```

(On 2026-10-21 at `bf9cadf04`: 20 of 20 runs on ext4, with or without `-race`; 12 of 20 with
`TMPDIR` on tmpfs. A variant sending serializable `Get`s as `root` through gRPC panicked from
`kvServer.Range` in 19 of 20 runs.)

**Cause:** [`applySnapshot`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/etcdserver/server.go#L1082-L1116)
swaps `s.be` and starts `go oldbe.Close()`, then restores the alarms (an fsync) and only then calls
`authStore.Recover(newbe)`. Until then the auth store's checks on gRPC goroutines
([`isOpPermitted`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/auth/store.go#L879-L883),
`CheckPassword`, `IsAdminPermitted`) read the old backend, whose close has reset its read
transaction to a nil `*bolt.Tx`
([`read_tx.go`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/storage/backend/read_tx.go#L103));
etcd's gRPC server has no panic recovery. `Recover` also writes `as.be` with no synchronization
with those checks (a data race under `-race`).

## Proof

yes: the verified fork moves the auth store before the old backend's close (`d52eec43e`,
`etc/goose.py`); `Spec/go_etcd_io/etcd/server/v3/auth/authStore__lockedReadTx.lean` specifies the
fix's locked read.

## Fix

**Branch**: `fix/etcd-auth-snapshot-closed-backend-panic` in `~/etcd-fixes/etcd-auth-snapshot-closed-backend-panic` (upamanyus/etcd, not pushed): 75d3f9bb0 test, 25dcea502 fix
**Base**: etcd-io/etcd@bf9cadf044f0531036a61c9b6dbeba8aef2a3b30

**PR draft**:

Title: server: close the old backend after the auth store moves off it

[`applySnapshot`](https://github.com/etcd-io/etcd/blob/bf9cadf044f0531036a61c9b6dbeba8aef2a3b30/server/etcdserver/server.go#L1082-L1114) starts closing the old backend before `authStore.Recover` moves the auth store to the new one. Permission checks on gRPC goroutines ([`isOpPermitted`](https://github.com/etcd-io/etcd/blob/bf9cadf044f0531036a61c9b6dbeba8aef2a3b30/server/auth/store.go#L879-L881), `CheckPassword`, `IsAdminPermitted`) read the auth store's backend, so in between they can lock a read transaction that the close has reset, and dereference a nil bolt transaction. This PR starts the close after `Recover` and `SetBackend`, and, since `Recover` replaces that backend without synchronizing with the checks (a race the new test reports under `-race`), makes `Recover` and the checks share a lock that a check holds until its read transaction is locked.

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

A reviewer may ask why both changes: the reorder alone leaves the `as.be` race (reported under
`-race` in 10 of 10 runs) and a tiny window for a check that loaded the old `as.be` just before
`Recover`; the lock alone does not help (10 of 10 panics). Alternatives considered: an
`atomic.Pointer` (removes the race, not the window), the backend refusing reads after close (every
caller changes, and the check would deny a valid user). mvcc's #22609 fixed the same hand-off in
`store.hash` the same way.

## Notes

- Security classification pending (the user's decision): a public filing exposes that, with auth
  on, any authenticated user's serializable read can crash a member during a snapshot restore. By
  the 2026-10-21 threat model (trusted clients) it is a robustness bug.
- INDEX-reviewed.md's plan: skip for now (a restart recovers).
- Same class, narrower windows, by code reading only: the maintenance `Snapshot` RPC takes
  `Backend()` twice and uses each after `bemu` is released; `store.hash` after #22609 still reads
  the old backend after `s.mu` is released (an error on a closed db, not a panic).
