---
upstream: reported
checked: 2026-11-01
links:
  - etcd-io/bbolt#1311 issue open: this bug, filed by us 2026-10-23
  - etcd-io/bbolt#1312 pr open: our fix (upamanyus/bbolt fix/bbolt-commit-meta-error-frees-reader-pages); CI green, two comments, no review (2026-11-01)
  - etcd-io/bbolt#262 issue closed: a fault in rollback's db.meta (a concurrent remap), a different cause
  - etcd-io/bbolt#152 issue closed: a rollback panic with NoFreelistSync, a different path
  - etcd-io/bbolt#331 issue closed: a crash between the data pages' sync and the meta's, a different path
blocks-proof: no
---

# bbolt: a read transaction's snapshot changes after a `Commit` fails once its meta page is written

A `Commit` that fails after its meta page reached the file (as when the `fdatasync` after that
write fails) frees the pages the transaction replaced while open read transactions still read
them: a later writer reuses them, and a read transaction that read `v1` reads another
transaction's `v3` for the same key. The "failed" commit also takes effect for new transactions.
Any application that keeps using the `DB` after such a `Commit` error with readers open; not
etcd, whose backend exits on any `Commit` error (`batchTx.commit`, `lg.Fatal`).

**Reproduction:** `TestTx_Commit_MetaWriteError_KeepsReaderSnapshot` in
[`issues/bbolt-commit-meta-error-frees-reader-pages/commit_meta_error_test.go`](bbolt-commit-meta-error-frees-reader-pages/commit_meta_error_test.go)
(the test of #1311, which fakes the write error after the meta page's bytes are written), copied
into the root of etcd-io/bbolt@a4ef19710eb7ddc41fd1155336baf331b5c57ba8 (2026-10-16), go1.27.3
linux/amd64:

```
$ go test . -run TestTx_Commit_MetaWriteError_KeepsReaderSnapshot -count=1
--- FAIL: TestTx_Commit_MetaWriteError_KeepsReaderSnapshot (0.00s)
    commit_meta_error_test.go:54:
        	Error:      	Not equal:
        	            	expected: "v1"
        	            	actual  : "v3"
FAIL	go.etcd.io/bbolt	0.015s
```

## Proof

no: the top-level adequacy proof needs no fix on the goosed fork for it; bbolt's `Commit` cannot have a spec that keeps open readers' snapshots when `writeMeta`
fails after the write reached the file; the bbolt proof (branch `bbolt`, unfinished) found it
stating `Commit`'s error paths, and `Tx.rollback`'s writer spec
(`Spec/go_etcd_io/bbolt/Tx__rollback_w.lean` there) requires the current meta to be the
transaction's old one. etcd's own proofs are unaffected (its backend exits on the error).

## Fix

**Branch**: `fix/bbolt-commit-meta-error-frees-reader-pages` in `~/etcd-fixes/bbolt-commit-meta-error-frees-reader-pages` (upamanyus/bbolt, pushed): 406c281 test, eb2b2e0 fix
**Base**: etcd-io/bbolt@a4ef19710eb7ddc41fd1155336baf331b5c57ba8

The PR (#1312) is open, at `eb2b2e0`. (The local branch in `~/etcd-bbolt` now points at
`84442b8`/`ccb6943`, not pushed: the same fix, and the test restores `writeAt` before asserting
the error.) Why the fix is in `rollback` and not `Commit`: `Update`'s deferred
rollback after a panic in the same window (a panicking `beforeSyncMetaPage` hook) is the same
code, and the fix covers it (checked in a copy: the reader reads `v1` with the fix, `v3` without).
