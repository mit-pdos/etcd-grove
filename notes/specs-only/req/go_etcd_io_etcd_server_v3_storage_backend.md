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

## from 3e

mvcc's store is stated over **its storage contract**, not over etcd's backend (the user, 2026-11-06:
"mvcc should respect the abstractions it builds on"): `Spec/go_etcd_io/etcd/server/v3/storage/mvcc/
ApiStorage.lean` (namespace `Mvcc`). 4a's job is to **prove that etcd's backend meets it**, and to
give the server (2d, 2e) what makes a store's storage from an opened backend. In plain terms:

1. **The contract `Mvcc.keyBackend B Pk`** (persistent; a bundle of triples, as `Schedule.isSched`) for
   `storageVal B` an etcd `*backend` (`B : MvccStorage`, the storage's names; `Pk` the batch lock's
   invariant, the client's: the commit hooks' resources). Its rows, over mvcc's part of the backend
   (`KeyData`: the `key` bucket's entries, the `meta` bucket's `scheduledCompactRev` and
   `finishedCompactRev`, whether the two buckets exist), which the other users' views must not
   overlap (the consistent index, the lessor's `beLeases`, membership, alarms, auth each have theirs):
   * `BatchTx()`/`ReadTx()` return fixed values (`kbBatchTx B`, `kbReadTx B`);
   * `ConcurrentReadTx()` and the shared `ReadTx`'s `RLock()`: a reader slot (`kbRdToks B 1`), a
     snapshot of the **visible** data (`kbData B D`: what the last `Unlock`'s write-back made
     visible) by the caller's atomic update (`kbObs`); `RLock` of a concurrent one is a no-op;
     `RUnlock()` gives the slot back; `UnsafeRange` on a read transaction reads its snapshot (`bkRange`:
     an empty end the key alone, else `[k, e)` in key order, cut at a positive limit; the slices
     read-only);
   * `LockInsideApply()`: the batch lock, the post-lock hook run under it (`hookRun Pk f Pre Q` at a
     share `storageHook B dq f`), the batch's view `kbLocked B D` at the visible data (atomic);
     `LockOutsideApply()`: the lock and `Pk`, no hook;
   * under the lock: `UnsafeCreateBucket(key|meta)` (`kbMade`), `UnsafePut`/`UnsafeSeqPut` of `key`
     (the bytes read-only: the backend keeps them), `UnsafePut` of a compaction key of `meta`,
     `UnsafeDelete` of `key` with the safe-range lock held (`kbSafeHeld`), `UnsafeRange` of the batch's
     view; `Unlock()` takes `kbLocked B D ∗ Pk` and makes `D` visible by the caller's atomic update
     (it may commit, under `Pk`);
   * `ForceCommit()`: the client's commit request `X ∗ storageReq B Pk X Y` to `Y` (the server's
     pre-commit hook saves its consistent index under `Pk`: 2d's item 3); `storageReq_true`;
   * `LockForSafeRangeDelete()`/`UnlockForSafeRangeDelete()`: `kbSafe B` ↔ `kbSafeHeld B`;
   * `Size()`, `SizeInUse()`, `OpenReadTxN()`: any `int64`, at any time (the store's metrics closures);
   * `kbLocked_held`: the batch lock's holder lends `kbHeld B` (**this is 3c's provisional
     `Lease.beTxHeld be`**: identify them, `be = GoInterface.ok (storageVal B)`).
   ```go
   tx := s.b.BatchTx(); tx.LockInsideApply()                        // kvstore_txn.go:176 (Write)
   tw.tx.UnsafeSeqPut(schema.Key, ibytes, d)                       // :256 (put)
   tx := s.b.ConcurrentReadTx(); tx.RLock()                        // :55-60 (Read)
   _, vs := tr.tx.UnsafeRange(schema.Key, revBytes, nil, 0)        // :119 (rangeKeys)
   s.b.LockForSafeRangeDelete(); tx.UnsafeDelete(schema.Key, keys[i]) // kvstore_compaction.go:31, 54
   s.b.ForceCommit()                                               // kvstore.go:213, 289
   ```
   Used by: every mvcc spec that touches the storage (`store.Read`, `store.Write`, `storeTxnWrite.*`,
   `store.updateCompactRev`, `store.scheduleCompaction`, `store.restore`, `NewStore`, ...).
2. **The storage's resources at the store's hand-over** (`Mvcc.mvccStorageFor B Pk h u`, transparent:
   the contract, `kbData B D` with `⌜mvccImage D h u⌝` (mvcc's meaning), the history's receipt, the
   delete right `kbSafe B`, `mvccReaderN` reader slots, the buckets made unless `D` is empty): the
   opener's (2e's `OpenBackend`/`OpenSnapshotBackend` over 4a's `New`) post must give the pieces 4a
   owns (`keyBackend`, `kbData B D` at the file's mvcc part, `kbSafe`, the slots, `kbMade`), so that the
   server, which knows the file's image is of `h` (its durable state), can assemble it. `storageRest
   B` (the data, `kbSafe`, the slots) is what a store gives back (after `Restore`, or `Close` with every
   reader token): **`Close` of the backend takes it** (no reader can start after the close:
   `issues/etcd-read-after-backend-close-panic.md`).
3. **The snapshot's image** (`Mvcc.mvccImage_obs.spec`): with the store's whole storage share and its
   state, mvcc hands the client an atomic read of the visible data (`kbObs B Φ`) that finds an image of
   the state's history. 4a's `Snapshot` spec should fire such an observation at a point where the data
   it snapshots (the last commit's) is the visible data (under the batch lock, a commit makes them
   equal: after `KV().Commit()`, until the next `Unlock`), so that 2d's merged snapshot learns its
   image is of `histAt γ c` (2d's item 4). A compaction job's batches (`Unlock` then `ForceCommit`)
   may run between: `mvccImage` admits a partly done compaction (`u`).
4. **The commit and a crash**: what a later open finds is the last commit's data (2d's item 3);
   mvcc's part of it is an image of the store's history at that commit (by 3 at the commit point).
