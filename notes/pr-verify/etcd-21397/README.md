# Reproduction Tests for `etcd-io/etcd#21397`

This directory contains standalone Go reproduction tests and logs for the verification of [`etcd-io/etcd#21397`](https://github.com/etcd-io/etcd/pull/21397) (`optimize scheduleCompaction`).

## Files

- `compaction_pr21397_bug_test.go`: Standalone unit test suite in package `mvcc` (`server/storage/mvcc`) reproducing three bugs introduced by PR `#21397`:
  1. `TestPR21397TombstoneKeyNeverDeleted`: Shows that `scheduleCompaction` in PR `#21397` never deletes superseded 18-byte tombstone keys (`<rev>t`) from the bbolt `key` bucket, because `BytesToRev(keys[i])` strips the `'t'` tombstone suffix and the consumer reconstructs a 17-byte non-tombstone key via `RevToBytes(rev, make([]byte, 8+1+8))` for `tx.UnsafeDelete`.
  2. `TestPR21397ReadBufferSkipsCommittedKeysAndCorruptsHash`: Shows that replacing `BatchTx.UnsafeRange` with `ReadTx.UnsafeRange(schema.Key, last, end, int64(batchNum))` skips committed bbolt keys and computes a wrong `KeyValueHash` whenever `readTx.buf` (`txReadBuffer`) holds uncommitted keys `<= compactMainRev`. `baseReadTx.UnsafeRange` takes `n` entries from `readTx.buf` (the newest revisions) and `batchNum - n` entries from bbolt (the oldest revisions starting at `last`), returning `append(k2, keys...)`; advancing `last` past `keys[len(keys)-1]` jumps over all committed bbolt keys between `k2[len(k2)-1]` and `keys[0]`.
  3. `TestPR21397StopcGoroutineLeak`: Shows that when `<-s.stopc` interrupts `scheduleCompaction`, the function returns without stopping or waiting for the spawned producer goroutine, which blocks forever on `toDelRevsChan <- rev` (or races with `s.b.UnlockForSafeRangeDelete()` and `b.Close()`, causing a `SIGSEGV` in `baseReadTx.UnsafeRange` when `CommitAndStop` sets `readTx.tx = nil`).
- `bug-test.log`: Output of running `compaction_pr21397_bug_test.go` against the PR branch `/root/etcd-pr/etcd-21397` (`pr-etcd-21397-goose-lean` at `3a370d91a871b2d22a6ae9f9706d3045103c33f4`), showing all three tests failing and reproducing the bugs.
- `baseline-test.log`: Output of running the same `compaction_pr21397_bug_test.go` against the baseline `goose-lean` branch (`bc9c3868ced67e518fb2fecba44ce0fa70b7303b`), showing all three tests passing prior to PR `#21397`.

## How to Run

Against the PR branch (`/root/etcd-pr/etcd-21397`):
```bash
cp notes/pr-verify/etcd-21397/compaction_pr21397_bug_test.go /root/etcd-pr/etcd-21397/server/storage/mvcc/
cd /root/etcd-pr/etcd-21397/server && GOTOOLCHAIN=go1.27.1 go test -v -run TestPR21397 ./storage/mvcc/...
rm /root/etcd-pr/etcd-21397/server/storage/mvcc/compaction_pr21397_bug_test.go
```

Against the baseline `goose-lean` branch (`/root/etcd`):
```bash
cp notes/pr-verify/etcd-21397/compaction_pr21397_bug_test.go /root/etcd/server/storage/mvcc/
cd /root/etcd/server && GOTOOLCHAIN=go1.27.1 go test -v -run TestPR21397 ./storage/mvcc/...
rm /root/etcd/server/storage/mvcc/compaction_pr21397_bug_test.go
```
