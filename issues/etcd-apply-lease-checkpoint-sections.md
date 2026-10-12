# server: a lease checkpoint entry is not persisted atomically with its consistent index

## Summary

`applierV3backend.LeaseCheckpoint` applies a `LeaseCheckpointRequest` by calling `Lessor.Checkpoint` once per checkpoint, and `lessor.Checkpoint`, when checkpoints are persisted (cluster version 3.6 or later, or `--experimental-checkpoint-persist`), writes each lease in its own critical section of the backend's batch transaction. A backend commit between two of those sections persists the entry's consistent index with only some of its checkpoints. If etcd crashes before the next commit, the entry is not applied again on restart, so the remaining leases keep a stale persisted remaining TTL and live longer than their TTL. That is the problem checkpoints are meant to solve (#9924). I found this while formally verifying etcd's apply path.

## What happens

References are to `main` at f061acd0902d489041448cdd19d71a345d27b9f5.

1. The server sets `txPostLockInsideApplyHook` (`server/etcdserver/server.go:412`, `getTxPostLockInsideApplyHook` at `server.go:2448-2455`). The hook runs each time the batch lock is taken inside apply (`batchTx.LockInsideApply`, `server/storage/backend/batch_tx.go:111-122`) and sets the consistent index to the entry being applied. A commit (the periodic one, `server/storage/backend/backend.go:475`, or the one at `Unlock` past the batch limit, `batch_tx.go:355`) takes the same lock and saves that index in its pre-commit hook. This is correct only if all of an entry's writes are made in one critical section: the commit then persists the index together with all of the entry's writes, or with none of them. On restart, entries at or below the persisted index are skipped.
2. The lessor's checkpoint scheduler proposes up to `maxLeaseCheckpointBatchSize` = 1000 checkpoints in one request (`server/lease/lessor.go:55`, `:669-683`).
3. `applierV3backend.LeaseCheckpoint` (`server/etcdserver/apply/backend.go:99-107`) calls `Lessor.Checkpoint(id, remainingTTL)` once per checkpoint. `lessor.Checkpoint` (`lessor.go:367-383`) persists the lease with `Lease.persistTo` (`server/lease/lease.go:55-61`), which takes `BatchTx().LockInsideApply()`, puts the lease, and calls `Unlock()`. A request with `n` checkpoints therefore makes `n` critical sections, and each one runs the hook with the same index.
4. A commit after section `k < n` persists the entry's index, the first `k` remaining TTLs, and the old records of the other leases (their remaining TTL from an earlier checkpoint, or 0 for the full TTL). If etcd crashes before the next commit, the entry is at or below the persisted index after restart, so it is not applied again. The other `n - k` leases are recovered with their old remaining TTL, so they expire later than they should.

The window is small: the commit must fall between two sections of one apply, and the crash must come before the next commit. When it happens, though, the leases outlive their TTL with no error reported.

## How to reproduce

The branch below adds these tests:

- `server/etcdserver/apply/lease_checkpoint_test.go`
  - `TestLeaseCheckpointOneCriticalSection` (subtests for 1, 2 and 10 checkpoints) applies a `LeaseCheckpoint` request through the `UberApplier`, with `CheckpointPersist` on and a post-lock hook that counts the critical sections. The request must take the batch lock inside apply exactly once.
  - `TestLeaseCheckpointCrashConsistency` demonstrates the loss without failpoints. The backend commits at every `Unlock` that has pending writes (batch limit 1), and the pre-commit hook saves the consistent index, as the server's backend hooks do. The post-lock hook does what the server's hook does and also copies the database file. Each copy is what a crash at that point would leave on disk. The test applies a checkpoint request for three leases and then a put. Every copy whose persisted consistent index is at or past the checkpoint entry must hold all three checkpoints.
- `server/lease/lessor_test.go`: `TestLessorCheckpointBatchPersistence` checks that one `Checkpoint` call persists every lease's remaining TTL in one critical section and ignores unknown leases. It reads the leases back through a new lessor on the same backend.

```
cd server && go test ./etcdserver/apply/ -run 'TestLeaseCheckpoint' -v
cd server && go test ./lease/ -run 'Checkpoint' -v
```

On `main` (the test files of the branch on top of `main`'s code):

```
TestLeaseCheckpointOneCriticalSection/checkpoints=2: expected: 1, actual: 2
    a LeaseCheckpoint request with 2 checkpoints took the batch lock inside apply 2 times
TestLeaseCheckpointOneCriticalSection/checkpoints=10: expected: 1, actual: 10
    a LeaseCheckpoint request with 10 checkpoints took the batch lock inside apply 10 times
TestLeaseCheckpointCrashConsistency: expected: 100, actual: 0
    crash 1: consistent index 4 persisted, lease 2's checkpoint is not
```

On `main`, the first section commits (index 4, lease 1's checkpoint), and the second section's hook sees a file with the entry's index and only lease 1's checkpoint. A restart from that file would skip entry 4 and recover leases 2 and 3 with their full TTL.

`TestLessorCheckpointBatchPersistence` uses the new signature, so it does not compile against `main`. Rewritten as `main`'s per-checkpoint loop, it fails with `Checkpoint took the batch lock 3 times, expected 1`.

## Expected

An applied entry's backend writes are atomic with its consistent index, which is what `txPostLockInsideApplyHook` is for (#13766). After a crash, every entry at or below the persisted index has all of its effects in the backend. For a `LeaseCheckpoint` entry, that means the remaining TTLs of all of its checkpoints.

## The fix

Branch `lease-checkpoint-one-section`, one commit (2a163496c04a46369598359aae70ae9c9f7197f2) off `main` (f061acd09), with the tests above:

- `Lessor.Checkpoint` now takes the request's checkpoints: `Checkpoint(cps []*pb.LeaseCheckpoint) error`.
- `lessor.Checkpoint` takes the lessor's mutex and, when checkpoints are persisted, `BatchTx().LockInsideApply()` once around the loop. It persists each lease with `Lease.unsafePersistTo(tx)`, split out of `persistTo`, which `Grant` still uses.
- `applierV3backend.LeaseCheckpoint` calls it once.
- `FakeLessor` (`server/lease`) and `SimpleLessor` (`etcdutl`) are updated.

The locks are taken in the same order as `Grant` (the lessor's mutex, then the batch lock).

The per-lease semantics are unchanged. On `main`, `lessor.Checkpoint` ignores an unknown lease and always returns nil, so the applier's early return on error never happens. The batch ignores unknown leases the same way, and the applier passes on its (nil) error.

After the fix:

- `go test ./server/lease/... ./server/etcdserver/apply/ ./server/etcdserver/` passes.
- `cd tests && go test ./integration/ -run Lease` passes, including `TestV3LeaseCheckpoint`.
- `etcdutl` builds.

## How the proof handles it

See `notes/STATUS.md`, the apply package (unit 1): the backend applier's `LeaseCheckpoint` triple takes a request with at most one checkpoint.

Found 2026-10-12 (apply unit 1), at etcd bc8b52a50 (`etc/goose.py`'s pin) and reproduced on upstream `main` f061acd09.
