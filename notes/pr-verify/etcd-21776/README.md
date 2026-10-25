# Reproduction & Probe Tests for `etcd-io/etcd#21776` (`[POC] feat: defragmented snapshots`)

## Files

- [`repro_pr21776_test.go`](repro_pr21776_test.go): Go unit test suite in package `backend` reproducing Findings 1, 2, and 3 on `etcd-io/etcd#21776` (`5809b379d943c9a9b6fb1a2f96f9810fea5514ac` on `pr-etcd-21776-goose-lean`).
- [`test.log`](test.log): Output of `go test -v -count=1 ./storage/backend -run TestPR21776`.

## How to Run

From the Goose fork worktree `/root/etcd-pr/etcd-21776` (commit `5809b379d943c9a9b6fb1a2f96f9810fea5514ac`):

```bash
cp notes/pr-verify/etcd-21776/repro_pr21776_test.go /root/etcd-pr/etcd-21776/server/storage/backend/
cd /root/etcd-pr/etcd-21776/server
go test -v -count=1 ./storage/backend -run TestPR21776
rm /root/etcd-pr/etcd-21776/server/storage/backend/repro_pr21776_test.go
```

## Summary of Tests

1. `TestPR21776Finding1_SnapshotDefragmentedHoldsBMuRLockAndStallsBatchTxDuringDefrag`:
   - Demonstrates that `(*backend).snapshotDefragmented` holds `b.mu.RLock()` across `os.CreateTemp`, `bolt.Open`, the entire `bolt.Compact(tmpdb, b.db, ...)` copy and fsyncs, and `tmpdb.Begin(false)`.
   - When `b.Defrag()` runs concurrently, it acquires `b.batchTx.LockOutsideApply()` first and then blocks on `b.mu.Lock()`, stalling all `b.batchTx.LockInsideApply()` writes and all concurrent `b.Snapshot()`/`b.Hash()` readers (blocked behind the queued `b.mu.Lock()` writer in `sync.RWMutex`) for the entire duration of `bolt.Compact`.
2. `TestPR21776Finding2_SnapshotDefragmentedIgnoresBoptsAndRunsWithNoSyncFalse`:
   - Demonstrates that unlike `(*backend).createDefragTmpDB` (which copies `options := *b.bopts` and sets `options.NoSync = true`), `(*backend).snapshotDefragmented` initializes `options := bolt.Options{}` with `NoSync: false, NoGrowSync: false, FreelistType: "", InitialMmapSize: 0`, ignoring `b.bopts` (even when `UnsafeNoFsync: true` is configured) and forcing `fdatasync` on every 16MB intermediate `bolt.Compact` commit to a throwaway temporary file.
3. `TestPR21776Finding3_DefragmentedSnapshotCloseSwallowsCloserErrors`:
   - Demonstrates that `(*defragmentedSnapshot).Close()` invokes `s.closer()` via `defer` where `closer` has signature `func()` (not `func() error`), swallowing `tmpdb.Close()` and `os.Remove(tdbp)` errors and returning `nil` to the caller.
