---
upstream: none
checked: 2026-11-15
links:
  - etcd-io/etcd@2e2963af6: related: made MinimalEtcdVersion read the latest snapshot entry, and added the retry of the WAL scan "after transient file removal" (the purge racing the scan, not the reopen)
blocks-proof: yes
---

# storage: a storage downgrade can panic, and lose WAL files, when the WAL purge runs during the WAL reopen

During a storage-version downgrade, the server checks the WAL's minimal version by closing the WAL
and reopening it (`storage.MinimalEtcdVersion`). Closing releases the locks on every WAL file. If
the WAL purge goroutine runs in that window and the member has more WAL files than `--max-wals`
since its last snapshot, it deletes the oldest ones, which the reopen still needs: the reopen
fails, and the member panics.

**Expected:** the purge should never delete a WAL file the open WAL still needs; it relies on the
WAL holding a lock on every such file (`fileutil.PurgeFileWithDoneNotify` skips locked files),
which the reopen breaks.

**Impact:** a member being downgraded (`etcdctl downgrade enable`, then the version monitor
migrating the storage schema down) with the purge on (the default, `--max-wals=5`) and more than
`--max-wals` WAL files since its last snapshot (large entries or a large `--snapshot-count`). The
window is the time between closing and reopening the WAL, against a purge every 30 seconds, so it
is rare. When it hits, the member crashes in the middle of the downgrade, and the files it needs
from its last snapshot record on are gone (whether it then restarts was not tested). Releases
with `MinimalEtcdVersion` reopening the WAL (v3.6 on).

**Reproduction:** `TestMinimalEtcdVersionConcurrentWithPurge` in
[`issues/etcd-storage-downgrade-reopen-purge-panic/reopen_purge_test.go`](etcd-storage-downgrade-reopen-purge-panic/reopen_purge_test.go),
copied (as `zz_reopen_purge_test.go`) into `server/storage` at
etcd-io/etcd@260e4e0457aa317681e8576339dc9ee1ebcabd66 (2026-11-14, `main`), go1.27.3 linux/amd64.
It runs the server's purge (`PurgeFileWithDoneNotify`, flock on, the default `--max-wals`) with a
1ms interval instead of 30s, and small segments (`wal.SegmentSizeBytes`, as etcd's own WAL tests
do), and calls `MinimalEtcdVersion` up to 200 times; it failed in 5 runs of 5, at upamanyus/etcd@3df9b265f too
(`file not found which matches the snapshot index '10'`):

```
$ (cd server && go test ./storage -run '^TestMinimalEtcdVersionConcurrentWithPurge$' -count=5)
--- FAIL: TestMinimalEtcdVersionConcurrentWithPurge (0.04s)
    zz_reopen_purge_test.go:91: after 1 reopens: MinimalEtcdVersion panicked: openAtIndex failed: [openAtIndex] openWALFiles failed: [openWALFiles] fileutil.TryLockFile failed: ofdTryLockFile failed to open ".../wal/0000000000000000-0000000000000000.wal" (open ...: no such file or directory)
--- FAIL: TestMinimalEtcdVersionConcurrentWithPurge (0.04s)
    zz_reopen_purge_test.go:91: after 1 reopens: MinimalEtcdVersion panicked: openAtIndex failed: [openAtIndex] openWALFiles failed: [openWALFiles] fileutil.TryLockFile failed: fileutil: file already locked
...
FAIL	go.etcd.io/etcd/server/v3/storage	0.092s
```

**Cause:** [`MinimalEtcdVersion`](https://github.com/etcd-io/etcd/blob/260e4e0457aa317681e8576339dc9ee1ebcabd66/server/storage/storage.go#L102-L121)
calls [`Reopen`](https://github.com/etcd-io/etcd/blob/260e4e0457aa317681e8576339dc9ee1ebcabd66/server/storage/wal/wal.go#L267-L273),
which `Close`s the WAL (unlocking every file) and then `Open`s it again; the storage's write lock
does not stop the server's [purge goroutine](https://github.com/etcd-io/etcd/blob/260e4e0457aa317681e8576339dc9ee1ebcabd66/server/etcdserver/server.go#L601-L607),
which deletes the oldest files beyond `--max-wals` that it can lock. It is reached from
[`schema.UnsafeMigrate`](https://github.com/etcd-io/etcd/blob/260e4e0457aa317681e8576339dc9ee1ebcabd66/server/storage/schema/schema.go#L69-L70)
on a downgrade.

## Proof

yes: a panic (and lost WAL files) on a downgrade with the default purge; the server's proof (C6)
cannot state `MinimalEtcdVersion` without a lock model, and ledger P8 proposes stating the purge as
a hypothesis or leaving it out of the closed theorem until then, i.e. a premise that excludes this.
SpecPlan's `storage.MinimalEtcdVersion.spec` (no panic under `diskOk`, "same records") is false
while the purge runs. `notes/wal-units/specgap.md` §3.3.

## Fix

Not written. `MinimalEtcdVersion` could read the entries through a second, read-only handle
(`wal.OpenForRead` at the snapshot entry, `ReadAll`, `Close`) while the open WAL keeps its locks,
instead of reopening it; the purge then cannot delete any of the files read.

## Notes

Searched upstream `main`'s history (`git log` on `server/storage/storage.go` and `wal.go`): the
only related change is `2e2963af6`, whose retry covers the purge removing a file during the scan of
snapshot entries, not during the reopen. GitHub's issue search was not run.
