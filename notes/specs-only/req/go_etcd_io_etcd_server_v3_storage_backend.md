# Requirements on `go.etcd.io/etcd/server/v3/storage/backend` and `storage/schema` (4a, 4b)

## from 2d

What the consistent index (`cindex`) and the apply thread need of the backend (4a) and the schema
(4b). `cindex/Api.lean` and `ApiApply.lean` declare provisional names for them:

1. **`beStoredCI be v`** (persistent): a read of backend `be`'s consistent index through
   `be.ReadTx()` (`schema.ReadConsistentIndex`, `UnsafeReadConsistentIndex`) returns `v` (`0`: none)
   as long as no commit writes it; a commit writes it only from the pre-commit hook's `UnsafeSave`
   of a non-zero index. Introduced by `OpenBackend`/`OpenSnapshotBackend` (2e) for the image's stored
   index. Used by: `consistentIndex.ConsistentIndex.spec`, `SetBackend.spec`, `NewConsistentIndex.spec`.
2. **`txStoredCI tx v`** (exclusive, with the batch transaction's lock): the transaction's view of
   the stored index; `schema.UnsafeUpdateConsistentIndex(tx, i, t)` sets it to `i` if `i ≠ 0` and
   `i ≥ v` (its `verify` check). Used by: `consistentIndex.UnsafeSave.spec`.
3. **The backend's commits save the state machine with its consistent index**: the pre-commit hook
   (2e's `BackendHooks.OnPreCommitUnsafe`) runs under the batch transaction's lock, so a commit's
   image is the state machine at `histAt γ c` with stored index `c` (2d's invariant: the in-memory
   index is the last entry whose writes are in the batch). A crash keeps the last commit's image.
4. **`backend.Snapshot`** (`beSnap bs γ k`): `s.be.Snapshot()` after `KV().Commit()` is the
   committed image (at `c`); `WriteTo` streams it, `Size` in `[0, 2^62)`, `Close` returns `nil`.
   Used by: `createMergedSnapshotMessage.spec`, `newSnapshotReaderCloser.spec`.
5. **`VerifyBackendConsistency(be, lg, true, buckets...)`** (`applyAll`): no panic on the server's
   backend (its checks pass, or `ETCD_VERIFY` is off: ApiBoot's `backendBootRes`).

## from 2e

Provisional names in 2e's modules, to be replaced by 4a's at integration:
1. `Snap.BeImage` (a type), `Snap.emptyImage img`, `Snap.beFile path o` (a closed database file's
   image, or no file: exclusive, timeless): a rename carries the image (`OpenSnapshotBackend`), an
   open of an absent path creates an empty one. Used by `OpenBackend.spec`, `OpenSnapshotBackend.spec`,
   `bootstrappedBackend.Close.spec`, `memberDisk`'s realization.
2. `ServerStorage.beOpen be path img` (the whole open token; its `Close` gives `beFile path (some
   img')`), `ServerStorage.beReadable be` (`Size`/`SizeInUse` at any time, also after `Close`:
   `BackendQuota.Available` runs on request goroutines), `ServerStorage.beTx tx` (the locked batch
   transaction the commit hooks write).
3. `EtcdServer.backendBootRes cfg` (the backend's slot of `NewServer`: the quota bbolt can map,
   `ETCD_VERIFY` unset).
   ```go
   be := serverstorage.OpenBackend(cfg, beHooks) // bootstrap.go:240
   ```

## from 3c

The lessor (`Spec/go_etcd_io/etcd/server/v3/lease/Api.lean`) declares provisional names for what it
needs of the backend (4a) and of the schema's lease bucket (4b); replace them by yours at
integration:

1. **`Lease.beOk be`** (persistent): `be.BatchTx()`, `tx.LockOutsideApply()` (no hook), `tx.Unlock()`
   and `be.ForceCommit()` may be called from any goroutine (the commit hooks' contracts are the
   backend's own). Used by: `NewLessor.spec`, `lessor.Recover.spec`, `lessor.initAndRecover.spec`
   (bootstrap and `applySnapshot`'s new backend).
   ```go
   tx := le.b.BatchTx(); tx.LockOutsideApply(); /* create, read all */ tx.Unlock()   // lessor.go:809-814
   le.b.ForceCommit()                                                                  // :834
   ```
2. **`Lease.beApplyTok be`** (exclusive, given back): the right to `LockInsideApply()` the batch
   transaction (running the post-lock hook: the apply thread's) and `Unlock()` it. Used by:
   `lessor.Grant.spec`, `lessor.Checkpoint.spec`, `Lease.persistTo.spec`.
   ```go
   tx := b.BatchTx(); tx.LockInsideApply(); defer tx.Unlock()   // lease.go:57-59 (persistTo)
   ```
3. **`Lease.beTxHeld be`** (exclusive): this thread holds the batch transaction's lock (mvcc's
   write transaction holds it from `Write()` to `End()`), so it may make unsafe writes. Used by:
   `lessor.Revoke.spec` (its `UnsafeDeleteLease` under the deleter's transaction, `lessor.go:359`),
   through `Lease.rdOk`.
4. **The lease bucket and the commit**: a commit (and a crash) keeps the bucket as written by then
   (`beLeases`, see the schema's file); `lessorState_bkt` lends the bucket back for the backend's
   close.
