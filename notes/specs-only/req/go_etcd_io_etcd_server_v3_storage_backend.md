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
2. **`Lease.beHook be Pk f`** (persistent; round 1, replacing `beApplyTok`): `be`'s batch lock has
   the invariant `Pk` and its post-lock hook is `f`: `LockInsideApply()` gives `Pk` and runs `f`
   (the caller's contract `Mvcc.hookRun Pk f Pre Q`, mvcc's), `Unlock()` takes `Pk` back. The same
   fact as mvcc's `mvccBackend γ q B Pk ∗ hookIs B f` for the storage `B` whose `storageVal` is `be`:
   identify them. Used by: `lessor.Grant.spec`, `lessor.Checkpoint.spec`, `Lease.persistTo.spec`
   (the grant's record committed with its entry's consistent index: 2d; `examples/mvccrand`'s
   check).
   ```go
   tx := b.BatchTx(); tx.LockInsideApply(); defer tx.Unlock()   // lease.go:57-59 (persistTo)
   ```
3. **`Lease.beTxHeld be`** (exclusive): this thread holds the batch transaction's lock (mvcc's
   write transaction holds it from `Write()` to `End()`), so it may make unsafe writes. mvcc's
   `kbHeld B` is the same for `storageVal B = be`: identify them. Used by:
   `lessor.Revoke.spec` (its `UnsafeDeleteLease` under the deleter's transaction, `lessor.go:359`),
   through `Lease.rdOk`.
4. **The lease bucket and the commit**: a commit (and a crash) keeps the bucket as written by then
   (`beLeases`, see the schema's file); `lessorState_bkt` lends the bucket back for the backend's
   close. **Writes under one lock hold land in one commit** (round 1): `Revoke`'s bucket delete is
   made under mvcc's write transaction's lock, with the keys' deletes; the crash image must keep them
   together (a restart finding a key whose record names a revoked lease would leave it forever:
   `restore`'s `Attach` fails and only logs, `kvstore.go:398-403`).

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

## from 2e, round 1

`backendBootRes_intro` (provisional in `ApiBoot`): from `backendEnvOk` (`ETCD_VERIFY` unset, a
program-start fact) and `QuotaBackendBytes ≤ 8 GiB` (bbolt maps `quota + quota / 10`): state your
slot's introduction at least this permissive.

## from 3e (round 1 repairs)

Changes to `Mvcc.keyBackend` (`ApiStorage.lean`) after review:
1. **A read transaction's `UnsafeRange`** (`KeyData.rtRange`) is what `baseReadTx.UnsafeRange` computes
   (`read_tx.go:75-121`): the read buffer's entries of the range cut at the limit, else bbolt's cut at
   the limit less them, followed by them; an empty end only as a `nil` slice; `Meta` only one key. The
   buffer's `Key` entries are above every committed one because a `Key` put's key is above every key
   present (the put row's premise: mvcc's revisions). `KeyData.clean` ("the buffer holds no `Key`
   entry"): a put clears it; an opened storage's data has it (`mvccStorageFor`), which `restore`'s
   chunked scan relies on (it reads the first `limit` entries in key order).
2. **Lock-only reads**: `kbRdToks_bare` turns a slot into `kbBareSlot B`, with which the shared read
   transaction's `RLock`/`RUnlock` work at any time, also after the backend's close (a mutex). **The
   backend's close takes `storageRest B n` for the slots not so kept** (`n = mvccReaderN - m`, `m` the
   store's `Rev` tokens): readers holding bare slots only lock and unlock the mutex.
3. **Slots**: the opener hands over `kbRdToks B mvccReaderN` with `mvccReaderN = mvccTokN + mvccOwnN`
   (`Api.lean`'s `mvccReaderN_eq`, `mvccTokN ≥ 2^28`): the backend's stock must cover it.
4. **Buckets**: `mvccStorageFor` asks `kbMade` only of the buckets that exist (a fresh member's backend
   has `Meta` already).
5. `mvccImage_obs` takes the store's open token; the shutdown law gives the final image
   (`mvccClosed_rest`), so a reopen of the closed file has its `mvccImage` (item 4 of "from 3e").

## from 4b

The schema (`Spec/go_etcd_io/etcd/server/v3/storage/schema/Api.lean`, namespace `Schema`) is stated
over **what it needs of a transaction**, not over the backend's predicates (as mvcc's `ApiStorage`):
every function taking a `tx` takes the caller's bundle `Schema.txRd tx S R` (single-key
`UnsafeRange`, `UnsafeForEach` in key order), `Schema.txRange tx S R` (interval `UnsafeRange` of a
whole bucket) and/or `Schema.txWr tx S R` (`UnsafePut`, `UnsafeDelete`, `UnsafeCreateBucket`), where
`R : Schema.View → IProp` is the **caller's** family (its share of the backend) and `S : Schema.Scope`
its buckets (whole) and keys (of a shared bucket: `Meta`). The struct methods that lock (`authBackend`,
`authBatchTx.Lock/Unlock`, `ReadConsistentIndex`, `CreateMetaBucket`) take the triples of the
backend calls as premises (`Schema.retOk`, `callOk`, `rdSect`, `wrSect`). So 4a owes **laws that
produce these bundles** for the transactions it hands out, for the parts it hands out:

1. **Per-part ownership** of the backend's data at the granularity the users need: whole buckets
   (`lease`, `alarm`, `members`, `membersRemoved`, `cluster`, `auth`, `authUsers`, `authRoles`, and
   mvcc's `key`), single keys of `meta` (`consistent_index`+`term`: 2d; `confState`: 2e;
   `scheduledCompactRev`+`finishedCompactRev`+`meta`'s existence: 3e). For each part: the batch view
   (what the batch transaction reads, its own writes included), the published view (what a read
   transaction begun now reads: equal to the batch view outside a write section of the part's
   writer, since `Unlock` writes the buffer back), and the durable image (the last commit's: what a
   crash leaves and the opener finds).
2. **Batch transaction, lock held** (`LockInsideApply`/`LockOutsideApply` to `Unlock`): `txRd`,
   `txRange` and `txWr` at the part's batch view (`UnsafeDelete` of `key` with the safe-range lock
   only, as mvcc's contract says; the schema never deletes from `key`).
   ```go
   tx := le.b.BatchTx(); tx.LockInsideApply(); defer tx.Unlock(); schema.MustUnsafePutLease(tx, &lpb) // lease.go:57-60
   ```
3. **Read transaction between `RLock` and `RUnlock`**: `txRd` at its snapshot of the part's published
   view; `txRange` only for `key` (etcd's read transactions panic on an interval range of a
   non-safe-range bucket: `nonissues/etcd-auth-readtx-getallroles-panics.md`). Also **the shared
   `ReadTx()` without `RLock` while the caller holds the batch lock** (`cindex.go:107`,
   `UnsafeConsistentIndex` from the post-lock hook): the batch lock excludes the read buffer's
   writers (write-back, commit), so `txRd` holds there too.
4. **The lock calls' triples** for `rdSect`/`wrSect`/`callOk`: `BatchTx()`/`ReadTx()` return fixed
   values (`retOk`); `RLock` takes a reader slot (the caller's `threadTok`, bounds plan) and gives
   the snapshot; `RUnlock` gives the slot back; `LockInsideApply` runs the post-lock hook
   (**`Schema.applyHook be Pre Q`**, provisional in the schema's Api: 3c's `beHook` with
   `Mvcc.hookRun`; replace by yours); `Unlock` publishes; `Commit` and `ForceCommit` commit (their
   pre-commit hook's resources are the lock invariant's, as 3e's `storageReq`).
5. **The two schema-owned parts of the names-only wrappers**, `Schema.alarmBkt be al` (the `Alarm`
   bucket holds the alarms `al`, `none`: absent) and `Schema.memberBkts be st` (the member buckets
   hold 2e's `ClusterSt`): realized over your part ownership (their records' encodings are in the
   schema's header); your opener's post (through 2e's `OpenBackend`/`OpenSnapshotBackend`) should
   give the parts so that 2e can introduce them for the image it opened.
6. **Bucket values are not constants**: `schema.Key` etc. hold `bucket` structs whose name slices
   are allocated at the package's initialization, so a contract over an opaque constant value per
   bucket (3e's `Mvcc.bucketVal`) cannot be proved of an execution. Quantify over
   `Schema.bucketAt b bv` (persistent; `bucketVars_init` gives it for the package's variables; the
   backend only calls `bv.ID()`, `Name()`, `IsSafeRangeBucket()`: `bucket.*.spec`).
Used by: every spec of `Spec/go_etcd_io/etcd/server/v3/storage/schema/`.

## from 3e (round 2: 4a's F1, F3)

Done in `ApiStorage.lean`: `kbLocked B D0 D` (session base and batch view); `Unlock` fires two nested
updates (`KeyData.mid D0 D`, then `D`); the `Key` put row's premise is above every key of `D0` and of
`D` (`Sess.fresh`); bucket arguments are any `bv` with `Schema.bucketAt b.bkt bv`. 4a's
`keyBackend_intro` should go through as F1/F3 propose.

## from 4b, round 1

The schema's bundles changed (review `reviews/4b-review-1.md`, F1-F4, F10); what 4a proves of its
transactions is now weaker in five ways (and its own drafts should take the same fixes):
1. **Bytes lent, not for good** (F1): a range's keys and values are bbolt's, lent against the view
   (`Schema.rangeK`: `lentIn dq …` with the wand back to `R V`); `UnsafeForEach`'s visitor gets
   `ks ↦*{dq} k`, `vs ↦*{dq} v` for its call only (4c's `txBytes` with `boltTx`). The outer slices
   (`append`s) are owned.
2. **A single-key range has a `nil` end** (F2): `txRd`'s row is `UnsafeRange(b, k, nil, limit)`;
   `txRange` takes `e = [] → es = slice.nil` (a non-`nil` empty end makes `baseReadTx.UnsafeRange`
   range with `MaxInt64` and panic outside `key`).
3. **`UnsafeForEach` visits each entry once, in some order** (F3, `Schema.entsAny`): the read
   transaction's is bolt's entries then the buffer's (`read_tx.go:54-76`).
4. **`UnsafePut` only of an entry bbolt accepts** (F4, `Schema.putFits`: non-empty key within
   `Bbolt.maxKeySize`, key and value within `Bbolt.bboltEntryMax`).
5. **The right to create a bucket is separate from its keys** (F10, `Scope.canCreate`): `txWr`'s
   create row needs `S.canCreate b`; existence (`V b = some m`) for a part of a shared bucket comes
   from your realization (a persistent "made" fact: these buckets are never deleted). mvcc's part
   is `Meta`'s two compaction keys with the create right; the CI's two keys without it.
6. **A lock taken by one component, a part written by another** (second tier 5): `lessor.Revoke`
   (`lessor.go:359`) writes the lease part while mvcc's write transaction holds the batch lock, so the
   lock-held fact must be lendable to other parts' owners (3e's `kbLocked_held`/`kbHeld`), and `txWr`
   of the lease part must follow from it. Snippet: `examples/specreq/schema/schema.go`
   (`ReqLeaseDeleteUnderTxn`).
