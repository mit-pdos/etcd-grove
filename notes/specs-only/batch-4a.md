# Batch 4a: etcd's storage backend (report)

Author agent, 2026-11-09. Everything builds (`etc/specs-build.sh --dir
Spec/go_etcd_io/etcd/server/v3/storage/backend`: OK, 100 modules); snippets: `cd examples && go vet
./specreq/backend/` clean, `gofmt -l` clean.

## Files

`Spec/go_etcd_io/etcd/server/v3/storage/backend/` (namespace `Backend`, new):
- `Api.lean`: the vocabulary (below). `Internal.lean`: the internal helpers' vocabulary (buffers,
  the physical batch state; no client imports it). `MvccStorage.lean`: the bridge law to mvcc's
  storage contract (only the server imports it; **blocked**, F1/F3 below).
- The API (full care): `New`, `DefaultBackendConfig`, `backend__{BatchTx, ReadTx, ConcurrentReadTx,
  ForceCommit, Snapshot, Hash, Size, SizeInUse, OpenReadTxN, Commits, Defrag, Close,
  SetTxPostLockInsideApplyHook, LockForSafeRangeDelete, UnlockForSafeRangeDelete}`,
  `batchTxBuffered__{Lock, LockInsideApply, LockOutsideApply, Unlock, Commit, UnsafePut,
  UnsafeSeqPut, UnsafeDelete, UnsafeCreateBucket, UnsafeDeleteBucket, UnsafeRange, UnsafeForEach}`,
  `readTx__{RLock, RUnlock, UnsafeRange, UnsafeForEach}`, `concurrentReadTx__{RLock, RUnlock, Lock,
  Unlock, UnsafeRange, UnsafeForEach}`, `snapshot__{Close, WriteTo, Size}`, `NewHooks`,
  `hooks__OnPreCommitUnsafe`, `VerifyBackendConsistency`, `Validate{CalledInsideApply,
  CalledOutSideApply, CalledInsideUnittest}`, `BackendConfig__mmapSize`, `newBoltLoggerZap`.
- Internal helpers (mirroring the code, two-line comments): `newBackend`, `newBatchTxBuffered`,
  `backend__{run, begin, unsafeBegin}`, `batchTx__{lock, Lock, LockInsideApply, LockOutsideApply,
  Unlock, unsafePut, UnsafePut, UnsafeSeqPut, UnsafeDelete, UnsafeDeleteBucket, UnsafeCreateBucket,
  UnsafeRange, safePending, commit}`, `batchTxBuffered__{commit, unsafeCommit, CommitAndStop}`,
  `unsafeRange`, `baseReadTx__UnsafeRange`, `readTx__{Lock, Unlock, reset}`, the buffers
  (`newBucketBuffer`, `bucketBuffer__{add, Range, ForEach, merge, dedupe, Len, Less, Swap,
  CopyUsed}`, `txBuffer__reset`, `txWriteBuffer__{put, putSeq, putInternal, reset, writeback}`,
  `txReadBuffer__{Range, ForEach, unsafeCopy, reset}`).
- Every one of the 91 old specs has a file; new: `DefaultBackendConfig`, `backend__Defrag`,
  `backend__Hash`, the three `UnsafeForEach`s, `Api`, `Internal`, `MvccStorage`.

Names-only (trusted) among them, each comment saying why it is true of the code: `Snapshot`,
`snapshot.WriteTo`/`Size` (bbolt's promoted `Tx` methods), `Hash`, `Defrag`,
`VerifyBackendConsistency`, the three `Validate*`, `newBoltLoggerZap`.

Snippets: `examples/specreq/backend/`: `parts.go` (`ReqWriteThenRead`, `ReqDeleteVisible`,
`ReqLentWrite`, `ReqBareRLock`), `commit.go` (`ReqReopen`, `ReqForceCommitDurable`,
`ReqHookWrites`), `snapshot.go` (`ReqSnapshotStream`), `ranges.go` (`ReqSeqRange`,
`ReqMetaSingle`).

## Exported vocabulary (`Api.lean`)

Model (transparent):
- `Image` (`made`, `ents`, and `clean`: a visible image's lower bound "the read buffer holds none of
  this bucket"), `Image.{empty, flushed, create, put, del, dropBkt, agree, agreeV}`.
- `Cell` (`bkt b`, `key b k`, `buf b`), footprints `Fp` (`all`, `none`, `union`, `bucket`, `key`,
  `bkt`).
- `Sess` (`base`, `cur`, `puts`): a batch session; `Sess.{init, put, del, create, dropBkt, fresh,
  putIn, mid, fin}`; `mid` is what readers see between a session's write-back and its commit.
- Ranges: `sortedEnts`, `single`, `btRange` (the batch transaction's), `rdRange` (a read
  transaction's: the buffer's part cut first and returned last, the split hidden unless the bucket is
  clean), `rdOrder`/`btOrder` (`ForEach` orders), `covers`, `BktInfo`; `imgBytes` (opaque: a file's
  bytes), `beReaderN` (sealed), `dbOpenOk cfg` (opaque environment premise).

Resources:
- `isBackend γ b p Pk` (persistent): the backend, its file path, its batch lock protecting `Pk`.
- `beOpen γ q` (fractional): open; sessions, commits, snapshots, defrag hold a share; `Close` all.
- `beCur γ F C` (exclusive per footprint): the batch image on `F`; `beVis γ F V` (exclusive, timeless,
  client-owned): the visible image on `F`; `beNoVis γ F` (persistent): untracked for good.
- `beSess γ q F S` (exclusive): the batch lock held in session `S`, publishing `F`.
- `beCurIs γ I` (ephemeral): the whole batch image at a commit point.
- `beHist γ L` (client-owned, timeless): the committed images in order (the file holds the last; a
  crash leaves one of them); `beCommitted γ I`, `beFinal γ I` (persistent).
- `beRdToks γ n` (counted), `beRd γ rt F V` (a begun read transaction); `beHook γ dq f`
  (fractional); `beDel γ`/`beDelHeld γ` (the safe-range delete right); `beMade γ b` (persistent);
  `beSnap γ s I bs`; `beFile p o` (a closed file's image); `bucketOk bk bi` (persistent); `envOk`
  (persistent: `ETCD_VERIFY` unset, the goroutines' thread pool).
- Contracts (transparent): `commitOk γ Pk` (the client's commit step: appends the batch image to
  `beHist` at each commit), `hookOk γ hk Pk` / `hookFnOk γ f Pk` (the pre-commit hooks: write under
  `Pk`, hand back the update of their published cells), `beReq γ Pk X Y` (a forced commit's per-call
  step), `hookRun Pk f Pre Q` (the post-lock hook), `visitOk`, `writeOk`, `ignOk`, `writable`,
  `bytesListAt`, `beNew` (what `New` hands the client's allocation step).

Laws (obligations): `isBackend_persistent`, `beOpen_fractional`, `beCur_{split, excl, agree,
freeze}`, `beVis_{split, agree, none, timeless, drop}`, `beNoVis_{persistent, mono, excl}`,
`beSess_{excl, widen, cur, vis, rd}`, `beCurIs_{cur, vis, flush}`, `beHist_{timeless, mem, final}`,
`beCommitted_persistent`, `beFinal_{persistent, cur}`, `beRdToks_split`, `beReaderN_ge`,
`beHook_{fractional, agree, persistent}`, `beDel_excl`, `beMade_{persistent, cur}`,
`beFile_{timeless, excl}`, `bucketOk_{persistent, id}`, `envOk_persistent`, `imgBytes_size`,
`beReq_{true, persistent}`. `MvccStorage.lean`: `keyBackend_intro` (with `mvccFp`, `keyDataOf`),
`beReaderN_mvcc` (the slot stock covers mvcc's `mvccReaderN` plus `2^27` for the other clients).

## Main changes from the old specs

- **One image owned by footprints**, client-owned in TaDa style (`beCur` the batch view, `beVis` the
  visible view), in place of `BParams`/`bkView`/`bView`/`rbPart`/`thinV`/`relog` and the
  deleting-versus-put session split: every client (mvcc, lessor, auth, membership, alarms, the
  consistent index, the hooks) owns its cells; a cell nobody reads through read transactions is
  dropped from tracking (`beNoVis`) and may then be written under another client's session (the
  lessor's delete in mvcc's write transaction).
- **`Unlock` publishes in two exact steps** (`Sess.mid` at the write-back, `Sess.fin` at the commit
  a deleting session always makes), in place of a logical view kept thin of the physical one.
- **The read buffer's hidden split stated** (`rdRange`): a read transaction's limited range of a
  safe-range bucket returns the buffer's part cut first, after bbolt's; exact (the plain cut range)
  when the bucket is known clean (`Image.clean`, set at commit points, `beCurIs_flush`).
- **Durability** in the client's hands: the commit history `beHist` (client-owned), appended by the
  client's commit step `commitOk` at every commit (periodic, forced, at `Unlock`, at `Close`, in a
  defragmentation); `beCommitted` from a snapshot or a forced commit; `beFinal` and `beFile` from
  `Close`; `New` over any file image (`beFile p o`: a restart, a received snapshot's file).
- **`Close`** takes the open token and every visible tracker (no read transaction can begin after
  it), gives back the file's image and the lock's resource; the reader slots stay with the clients
  (in-flight readers finish first; a lock-only `RLock` is fine after the close).
- **Relaxed**: no thread token on `New` (the pool in `envOk`); no panic disjunct (`dbOpenOk`, the
  environment premise); no premise for a fatal path (`lg.Fatal` never returns: a missing bucket, an
  empty key, a bbolt error); hooks of any shape (`hookOk` per `Hooks` value, `nil` allowed); any
  batch limit and interval; non-blocking defragmentation in scope (`Defrag`, the safe-range lock).
- **Added premises the code needs**: `Sess.fresh` for sequential puts and safe-range puts (the
  write-back sorts only non-sequential buckets; a safe-range bucket's buffered keys must be above
  bbolt's); `bboltEntryMax` on puts (4c's); `beDelHeld` on safe-range deletes (a non-blocking
  defragmentation would copy them back); `limit = 1` or a `nil` end on a non-safe-range bucket's
  read-transaction range (`read_tx.go:86` panics otherwise).

## Callers' needs: how they are met (provisional names to replace at integration)

- **2d**: `beStoredCI`/`txStoredCI` are 4b's over `beVis`/`beCur` of `meta`'s index cells (the hook
  writes them at commits, `hookOk`); item 3 (a commit's image is the state at `c`) is the server's
  `commitOk` step (its invariant over `beHist`, checked at each commit with `beCurIs` and its parts);
  item 4: `beSnap bs γ k` is `beSnap γ s I bs ∗ beCommitted γ I` (with 2d's invariant on `I`);
  `Size` the bytes' length (`< 2^48`), `Close` `nil`; item 5: `VerifyBackendConsistency.spec`
  (`envOk`).
- **2e**: `Snap.BeImage` is `Backend.Image`, `Snap.emptyImage img` is `img = Image.empty`,
  `Snap.beFile` is `Backend.beFile`; `ServerStorage.beOpen be p img` is `isBackend γ b p Pk ∗
  beOpen γ 1 ∗` the parts and history at `img` (`beNew`'s, after the client's step); `Close` gives
  `beFile p (some I)`; `beReadable` is `isBackend` (`Size`/`SizeInUse` at any time); `beTx` is the
  hooks' session (`hookOk`); `backendEnvOk` is `envOk`; `backendBootRes`'s introduction from
  `envOk` and the quota needs `ServerStorage.diskOk → dbOpenOk cfg'` for `OpenBackend`'s
  configuration (2e's trusted `OpenBackend` can state it: `dbOpenOk` is the environment premise
  of the open, the mmap of the quota's size included).
- **3c**: `beTxHeld be` is the session (`beSess γ q F S`, lent); `beApplyTok be` is `beHook γ dq f`
  with the apply's `hookRun`; **`beOk be` cannot stay persistent**: `LockOutsideApply` and
  `ForceCommit` after the backend's close are fatal or panic, so the lessor needs an open share
  (`isBackend ∗ beOpen γ q`), given back before the close (Q5).
- **3e**: `keyBackend_intro.spec` (`MvccStorage.lean`), blocked by F1/F3 (`req/..._mvcc.md`, "from
  4a"); `storageRest` back to the backend's `Close` (the visible tracker; slots are not needed back,
  so `kbBareSlot` is a plain slot); the slots by `beReaderN_mvcc` (round-1 item 3: mvcc's constant
  must stay below `2^30 - 2^28`); the read buffer's split and `clean` by `rdRange` and
  `Image.clean`; the snapshot's image by `beCommitted` (no observation under the lock is possible).
- **4b**: `req/..._schema.md`, "from 4a": the bundles over this vocabulary; their `UnsafePut` row
  needs the entry bound, their read-transaction `ForEach` row is not in key order; `bucketOk` from
  `bucketAt`; `applyHook` is `LockInsideApply.spec`; reads under the lock: `beSess_rd`.

## Findings (for 3e, 4b; no Go bug)

- **F1 (blocks `keyBackend_intro`)**: mvcc's `Unlock` row fires one update, but the backend shows a
  session's puts before its deletes (the compaction's last batch: `finishedCompactRev` visible with
  the batch's deleted keys still there). 3e to choose: two updates, or a read range tolerant of the
  session's deleted keys.
- **F3 (blocks it too)**: mvcc's `key` put row needs the key above the keys the session began with,
  not only those it still has.
- **F2 (4b)**: a read transaction's `UnsafeForEach` is two sorted runs, not key order.
- **F4 (4b)**: the schema's put row lacks bbolt's entry bound.
(3e had already fixed the limited-range order, `rtRange`, and the reader slots after the close.)

## Functions left out (no old spec; nothing in the sketches needs them)

`NewDefaultBackend`, `WithMmapSize`, `WithTimeout` (etcdutl and `server/verify` only); the
defragmentation's internals (`defrag`, `defragBlocking`, `defragNonBlocking`, `createDefragTmpDB`,
`cleanupTmpDB`, `finishDefrag`, `defragdb`, `defragdbAndTrackLastKeys`, `catchUpDefrag`,
`verifyBulkCopyConsistency`, `hashBucketUpToKey`: covered by `Defrag`'s trusted spec);
`RegisterSafeRangeBucket`/`isRegisteredSafeRangeBucket` (the schema's init, 4b); `zapBoltLogger`'s
methods (4c's logger contract); the embedded `batchTx.Commit`/`CommitAndStop`/`UnsafeForEach`,
`unsafeForEach`, `baseReadTx.UnsafeForEach` (overridden or covered by the promoted specs);
`verifyLockEnabled`, `insideApply`, `insideUnittest`, `unsafeVerifyTxConsistency` (off with
`envOk`); the metrics.

## Open questions for the user

1. **F1** (mvcc's contract, 3e's to change; the user's call if it widens mvcc's statements): two
   visible updates per `Unlock` (exact: mvcc's `kbLocked` carries the session's base and puts), or
   one update and read ranges of `key` that may include entries the session deleted (smaller client
   statements; a persistent "deleted" mark). Recommended: two updates (no new mark, and the
   compaction's last batch is the only session that needs the middle state).
2. **Durability through the lock's resource**: the client chooses at `New` the batch lock's resource
   `Pk` and its commit step `commitOk` (append the batch image to its history), which every commit
   (including the run loop's background ones) runs. This departs from pure TaDa as a lock invariant
   does (mvcc's `Pk` already does); the alternative, a persistent atomic update handed to `New`, is
   the same thing spelled differently. Accept?
3. **`UnsafeNoFsync`**: with it set, bbolt promises nothing after a crash (4c's `BoltSt.commit`), so
   `beHist`'s crash meaning is void. The specs take no premise (the mode changes only what a crash
   leaves); a closed theorem about crashes must assume it off. Record it as a mode of `isBackend`?
4. **Fatal paths**: puts into a missing bucket, an empty key, a failed commit `lg.Fatal` (never
   returns, W0's zap spec), so the specs take no premise for them. Is an exit acceptable in the
   closed theorems here, or should such paths be excluded by premises (`beMade` on writes)?
5. **3c's `beOk`** must become a fractional open share (the lessor's `LockOutsideApply` and
   `ForceCommit` after the close are fatal); the server's shutdown then collects it before the
   backend's close.
6. **Thread accounting**: every commit forks a rollback goroutine that waits for the interval's
   readers; `envOk` holds a handle on the bounds plan's thread pool they borrow from. A goroutine of a
   closed backend may outlive its `Close` (it waits for no reader then, but the logic cannot bound
   when it ends), so the pool is global, not per backend.

## `req/` sections written

`go_etcd_io_bbolt.md` (new; "from 4a": `Open`'s success premise, the logger, transactions, commit's
update, cursors' bytes' lifetime, `WriteTo`/`Size`, `Close`, the flat image), 
`go_etcd_io_etcd_server_v3_storage_mvcc.md` ("from 4a": F1, F3, the lent lock, the snapshot's image,
readers after the close), `go_etcd_io_etcd_server_v3_storage_schema.md` ("from 4a": the bundles over
this vocabulary, F2, F4, `bucketOk`, `applyHook`, `beSess_rd`, `meta`'s existence).

## Round 1 repairs (review `reviews/4a-review-1.md`)

All 101 modules build (`--dir Spec/go_etcd_io/etcd/server/v3/storage/backend`, with the new
`Durable.lean`); snippets re-vetted (`go vet`, `gofmt -l` clean).

- **T1 (concurrent reads after a commit)**: the review's option (a), the weakest true statement that
  serves mvcc and the server. `ConcurrentReadTx` takes a footprint disjoint from the hooks' cells
  (`beHookFp γ Fh`, fixed at `New`); a concurrent read transaction's `UnsafeRange` is stated for single
  keys only (`es = nil`), with `lingerSingle`: a key of the view reads its value, a key the view lacks
  reads nothing or a value it had before a delete (the stale buffer copy); its `UnsafeForEach` visits
  every entry of the view once and maybe lingering ones (`rdOrderL`). The shared `ReadTx` stays exact
  (its buffer is live). mvcc's concurrent range row must weaken the same way: `req/..._mvcc.md`,
  "from 4a, round 1" (e). The fork fix is open question 7.
- **T2 (hooks' leftovers)**: `hookOk γ hk Fh Pk` restricts the hooks to puts of `Fh` (`hookWrites`);
  `Image.clean` now means "nothing but the hooks' leftovers, at the committed values"; a shared read
  transaction's range of a safe-range bucket takes a bucket with no `Fh` cell; `Unlock`'s sketch says
  the write-back also flushes the last commit's leftovers.
- **T3 (bytes)**: range results are lent (`bytesListAt … dq`, `rangeRes kl vl l R`, the wand back to
  the transaction resource: `beRd`, `beSess`, `btPhys`, `curOver`); `visitOk` lends the visitor its
  bytes for the call. The buffer's internal ranges keep `DFrac.discard` (the session's put bytes).
- **T4 (introductions)**:
  - `bucketOk` is transparent (the `ID`/`Name`/`IsSafeRangeBucket` bundle; 4b proves it of
    `bucketAt`); id uniqueness is `beBkt γ bi` from `New`'s declared set `Bs` (`bktsOk`); every bucket
    argument is `bkt γ bk bi`.
  - `Durable.lean` (new): `imgOf`, `beFile_of` (from 4c's `fileHolds`: `New` can be called, also over
    a received snapshot's file), `beFile_none`, and the crash law `beCrash` (from `beDurInv`,
    `beSynced` and the client's `beHist`, a crash leaves one of the committed images; over 4c's
    `boltCrash`). The `[HasExt osFsExt]` binder on the realized predicates is a recorded gap.
  - `envOk_intro` from `etcdVerifyUnset` (2e's `backendEnvOk`).
  - `safeRegOk` (the safe-range registry, for a non-blocking defragmentation): `New` takes it when so
    configured; its introduction is 4b's (`req/..._schema.md`, round 1, item 2): a recorded gap.
- **T5 (the bridge)**: `MvccStorage.lean` rebuilt against 3e's round 2 (`Schema.bucketAt`,
  `kbLocked B D0 D`, the nested two-step `Unlock`, the freshness over `D0`/`D`), with the open share,
  the hooks' disjointness, `kbHeld` pinned to `mvccFp`, `schemaBkts`, and the way back at the
  trackers' last data (which `Close`'s new `Image.agree F I V` ties to the closed file). Still blocked
  on five mvcc rows ((a) an open share, (b) a `key` delete of a key not put in the session, (c) the
  entry bound, (e) the concurrent range row, (f) lent bytes), written in `req/..._mvcc.md`, "from 4a,
  round 1", with (g) `hookRun` holding the session.
- **T6 (the post-lock hook's read)**: `hookRun γ q Pk f Pre Q` runs `f` holding the just-begun
  session and gives it back, so the hook can use `beSess_rd` (`cindex.go:102-110`).
- **Second tier**: S1 (the hook's session's base is `Sess.mid` inside an `Unlock`; `beSess_vis`'s
  unchanged-cell conjunct dropped, so `beSess_rd` lends what readers then see); S2 (a common
  assumptions header: `dbOpenOk`, `envOk`, the buckets, the entry bound, the hooks' footprint;
  `ReqHookWrites`'s tracker in an invariant; `ReqForceCommitDurable` checks the write; `ReqSeqRange`'s
  concurrent read single-key); S3 (`more.go`: `ReqForEach`, `ReqCompactionBatch`, `ReqPostLockHook`,
  `ReqMaintenance` (Defrag, Hash, sizes after `Close`), `ReqOpenSnapshotFile`); S4 (no pool: `New`
  takes the run loop's `threadTok`, `Close` returns it; rollback goroutines by `wp_fork_tok_self`;
  Q6 closed); S5 (`bbAt bb l w` with a writable flag, `add`/`merge` need it, `CopyUsed` gives a
  non-writable copy, `mergeOk` is the code's test over sorted parts); S6 (`Mlock` a filed scope
  restriction in `New`; `UnsafeNoFsync` recorded, `beSynced` only when off: Q3 closed); S7 (`Close`
  takes trackers disjoint from `Fh`: the hooks' cells untracked first); S8 noted.
- `req/` written: `..._mvcc.md` and `..._schema.md` ("from 4a, round 1"), `..._lease.md` ("from 4a":
  `beOk` becomes an open share).

New open question:
7. **The stale read-buffer copy** (T1): the fork's one-line fix (`bufVersion++` in `readTx.reset`,
   branch `fix/etcd-backend-read-buffer-cache-stale-after-commit`) would make concurrent reads exact
   again (ranges with an end, hook cells). Take it into the pinned fork (a code change), or keep the
   weaker specs?
