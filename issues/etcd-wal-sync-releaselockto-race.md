---
upstream: none
checked: 2026-11-15
links:
blocks-proof: yes
---

# wal: Sync races with ReleaseLockTo on a follower that receives a snapshot while it takes its own

`(*WAL).Sync` reads the WAL's list of locked segment files without taking the WAL's mutex, while
`(*WAL).ReleaseLockTo` rewrites that list under the mutex. etcd's server calls the two
concurrently: on a follower that receives a snapshot from the leader, the raft goroutine calls
`storage.Sync()` after saving it, while the apply goroutine may still be finishing the previous
batch and taking its own snapshot (`storage.SaveSnap` then `storage.Release`). Both hold only
the storage's read lock. The race detector reports a data race on the slice header.

**Expected:** `WAL.Sync` should be safe to call concurrently with the WAL's other methods, as
`Save`, `SaveSnapshot`, `ReleaseLockTo` and `Close` are (each takes `w.mu`), and as
`storage.Storage` assumes when all its methods but `Close` and `MinimalEtcdVersion` take only a
read lock.

**Impact:** a follower that receives a snapshot (`MsgSnap`: a slow or new member) while its apply
goroutine takes a snapshot (every `--snapshot-count` applied entries). The default configuration
reaches it. In practice the read is of a slice header (pointer and length) torn by the concurrent
write: `tail()` can index `w.locks` with the old length on the new base pointer, which reads past
the slice's end. Rare, but it is undefined behavior under the Go memory model, and every release
since `Sync` was added (2019, `50517039a`) has it.

**Reproduction:** `TestStorageSyncConcurrentWithRelease` in
[`issues/etcd-wal-sync-releaselockto-race/sync_release_race_test.go`](etcd-wal-sync-releaselockto-race/sync_release_race_test.go),
copied (as `zz_sync_release_race_test.go`) into `server/storage` at
etcd-io/etcd@260e4e0457aa317681e8576339dc9ee1ebcabd66 (2026-11-14, `main`), go1.27.3 linux/amd64.
The test passes without `-race`; it fails the same way at upamanyus/etcd@3df9b265f.

```
$ (cd server && go test -race ./storage -run '^TestStorageSyncConcurrentWithRelease$' -count=1)
==================
WARNING: DATA RACE
Write at 0x00c0002fc760 by goroutine 56:
  go.etcd.io/etcd/server/v3/storage/wal.(*WAL).ReleaseLockTo()
      server/storage/wal/wal.go:947 +0x485
  go.etcd.io/etcd/server/v3/storage.(*storage).Release()
      server/storage/storage.go:78 +0x15b
  ...
Previous read at 0x00c0002fc760 by goroutine 55:
  go.etcd.io/etcd/server/v3/storage/wal.(*WAL).tail()
      server/storage/wal/wal.go:1073 +0xdb
  go.etcd.io/etcd/server/v3/storage/wal.(*WAL).sync()
      server/storage/wal/wal.go:886 +0xf0
  go.etcd.io/etcd/server/v3/storage/wal.(*WAL).Sync()
      server/storage/wal/wal.go:902 +0xaa
  go.etcd.io/etcd/server/v3/storage.(*storage).Sync()
      server/storage/storage.go:99 +0x89
  ...
--- FAIL: TestStorageSyncConcurrentWithRelease (0.04s)
    testing.go:1867: race detected during execution of test
FAIL	go.etcd.io/etcd/server/v3/storage	0.079s
```

**Cause:** [`Sync`](https://github.com/etcd-io/etcd/blob/260e4e0457aa317681e8576339dc9ee1ebcabd66/server/storage/wal/wal.go#L901-L903)
calls `sync()`, which reads `w.tail()`
([`wal.go#L886`](https://github.com/etcd-io/etcd/blob/260e4e0457aa317681e8576339dc9ee1ebcabd66/server/storage/wal/wal.go#L886),
[`tail`](https://github.com/etcd-io/etcd/blob/260e4e0457aa317681e8576339dc9ee1ebcabd66/server/storage/wal/wal.go#L1072-L1077)),
without `w.mu`; [`ReleaseLockTo`](https://github.com/etcd-io/etcd/blob/260e4e0457aa317681e8576339dc9ee1ebcabd66/server/storage/wal/wal.go#L909-L950)
writes `w.locks = w.locks[smaller:]` under `w.mu`. The server's raft goroutine calls
[`storage.Sync`](https://github.com/etcd-io/etcd/blob/260e4e0457aa317681e8576339dc9ee1ebcabd66/server/etcdserver/raft.go#L269)
for a received snapshot, after handing the previous batch to the apply goroutine, which runs
[`snapshot()`](https://github.com/etcd-io/etcd/blob/260e4e0457aa317681e8576339dc9ee1ebcabd66/server/etcdserver/server.go#L2117-L2123)
(`SaveSnap`, `Release`) once that batch's disk writes are done
([`applyAll`](https://github.com/etcd-io/etcd/blob/260e4e0457aa317681e8576339dc9ee1ebcabd66/server/etcdserver/server.go#L989-L991)),
concurrently with the next batch; [`storage`](https://github.com/etcd-io/etcd/blob/260e4e0457aa317681e8576339dc9ee1ebcabd66/server/storage/storage.go#L74-L100)'s
`Release` and `Sync` both take only `st.mux.RLock`.

## Proof

yes: Goose's semantics makes a racy load a failure, so the server's proof (C6) needs a fork fix
(`Sync` takes `w.mu`, or `storage.Sync` takes the write lock). **Fixed in the fork** (2026-11-15, the user's decision):
upamanyus/etcd `goose-lean-walfs` `e115818f5` ("wal: take w.mu in Sync", `fix.patch` with this test as
`server/storage/sync_release_race_test.go`; `notes/wal-fsext-fork/0006-*.patch`); the test passes under `-race` there. Ledger P2
(`notes/specs-only/ledger.md`, 2026-11-15) and `notes/wal-units/specgap.md` §3.1.

## Fix

[`fix.patch`](etcd-wal-sync-releaselockto-race/fix.patch) (against
etcd-io/etcd@260e4e0457aa317681e8576339dc9ee1ebcabd66; the test passes with it under `-race`, and
so do `server/storage` and `server/storage/wal`): `Sync` takes `w.mu` like the other exported
methods. The lock is the one `Save` already holds across its own `sync()`, so it adds no new
ordering; the raft goroutine's `Sync` may wait for an apply-side `SaveSnapshot`/`ReleaseLockTo`,
which are short.

## Notes

Searched upstream `main`'s history (`git log` on `server/storage/wal` and `storage.go`, by
pickaxe and message): `Sync` has had no lock since it was added (`50517039a`, "etcdserver/*,
wal/*: add Sync method", for etcd-io/etcd#10219), and no fix or report touches it. GitHub's issue
search was not run.
