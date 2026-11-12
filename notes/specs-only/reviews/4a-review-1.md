# Batch 4a (storage backend): review, round 1 (provability and completeness)

Reviewer agent, 2026-11-09. Targets: `SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/backend/` (`Api.lean`,
`Internal.lean`, `MvccStorage.lean`, 97 specs), `examples/specreq/backend/`, `## from 4a` in
`req/*.md`, the report `batch-4a.md`. 4a's draft is `51a613f05c`; HEAD is `55a0ad7fb6` (3e round 2,
`a0e2b76347`, landed after the draft), and the worktree has 4b's uncommitted round-1 changes
(`req/..._backend.md`, "from 4b, round 1"). Go: `.lake/src/server/storage/backend/*.go`. Checked:
`etc/lean-check.py` on `MvccStorage.lean`; `go vet ./specreq/backend/` and `gofmt -l` (both clean).

## Verdict

**Not done. Seven first-tier findings.**
- The model is right where the author checked it most carefully: the write-back, the two-step
  `Unlock`, `rdRange`, `btRange`, `rdOrder` (F2), `Sess.fresh` and the safe-range lock all match the
  code.
- What breaks:
  - the read side's snapshot claim, through the cache of the read buffer (T1) and the hook's
    leftovers (T2);
  - the lifetime of the returned bytes (T3);
  - four pieces of vocabulary that no law introduces (T4);
  - the post-lock hook's read (T6);
  - the bridge, which does not build at HEAD and has five more obstacles beyond F1/F3 (T5).
- F1/F3 themselves: with 3e's two nested updates and its freshness premise, the `Unlock` and put rows
  go through. One more premise is needed on the `Key` delete row (T5b).
- No new Go bug. The facts that matter are already filed:
  - `nonissues/etcd-backend-read-buffer-cache-stale-after-commit.md`;
  - `issues/etcd-read-after-backend-close-panic.md`;
  - `issues/bbolt-large-values-leaf-unreadable.md`.

## What is good

- **The write-back and two-step publication** (`Sess.mid`, `Sess.fin`, `batch_tx.go:328-360`) are
  exact.
  - The puts reach readers at the write-back and the deletes at the commit, which a deleting session
    always makes (`pendingDeleteOperations`).
  - `mid` = "the last value put, over the base" is right even for a put followed by a delete of the
    same key (the buffer keeps the put until the commit).
  - A session with nothing pending but leftover counts (`pending ≠ 0` from an earlier put-only
    session) is covered: its `mid` is its base.
- **`rdRange` matches `baseReadTx.UnsafeRange`** (`read_tx.go:78-122`) case by case:
  - a `nil` end forces the limit to 1;
  - the buffer's part is cut at `limit` and returned whole if it fills the limit;
  - otherwise bbolt's part is cut at `limit - n` and the buffer's part is appended after it;
  - a limit ≤ 0 means no limit;
  - the panic premise `bi.safe ∨ es = nil ∨ limit = 1` is exactly what `:86` needs.

  I checked the equivalence with 3e's `KeyData.rtRange`: identical.
- **`btRange`** (`unsafeRange`, `batch_tx.go:206-226`), **`btOrder`** and **`rdOrder`** (two sorted
  runs, each entry once, `read_tx.go:54-76`) are right. F2 is a real finding against 4b.
- **`Sess.fresh`** (above every key of the base and of the current image) is what the read buffer's
  sortedness needs:
  - `putSeq` neither sorts nor deduplicates;
  - `merge` deduplicates only when the old buffer's last key is ≥ the new buffer's first.

  It is also what keeps a safe-range bucket's buffered keys above bbolt's. F3 is right, and 3e has
  taken it.
- **The safe-range lock on safe-range deletes and bucket drops** is exactly what
  `defragNonBlocking`'s catch-up needs (`backend.go:694-700`, `:986-1016`).
- **Close takes every tracker.** Footprint-owned trackers, with `Close` taking all of them, are a
  sound answer to the read-after-close panic. A read after `CommitAndStop` reaches
  `baseReadTx.tx.Bucket` on a nil `*bolt.Tx` (`read_tx.go:103`), and bare `RLock`/`RUnlock` stays
  legal through `beVis_none`.
- **Two linearizations hold, though neither is spelled out.**
  - The session's base equals the batch image when `LockInsideApply` or `LockOutsideApply` returns:
    every `Unlock` with something pending writes back, every delete commits, and the hook's leftovers
    in the write buffer equal the committed values.
  - The `Unlock` updates fire inside `readTx.Lock`.
- **The trusted specs** (`Snapshot`, `WriteTo`, `Size`, `Hash`, `VerifyBackendConsistency`,
  `Validate*`, `Defrag`) are true of the code as stated:
  - `Tx.Size` is the length `WriteTo` writes;
  - `Hash` on a closed database returns `ErrDatabaseNotOpen` and needs no open share;
  - `Defrag`'s post says nothing it cannot keep.

  `Snapshot`'s change from an observation to `beCommitted` is the right call: a run-loop or
  compaction commit can land between `Commit()` and `Begin` (`backend.go:381-386`).
- **Fatal paths** need no premise against W0's `Logger.Fatal` (it never returns). The reasoning
  that `ForceCommit` and the locks still need an open share (a hook's `UnsafePut` on a closed bbolt
  transaction dereferences `tx.db`, a panic, not a fatal) is correct.

## First tier

### T1. A concurrent read transaction's view is not the visible image after a commit (unsound)

- **Principle:** sound, true of the code.
- **Targets:** `backend__ConcurrentReadTx.lean`, `concurrentReadTx__UnsafeRange.lean`,
  `concurrentReadTx__UnsafeForEach.lean`.
- **Mechanism:**
  - `ConcurrentReadTx` reuses `txReadBufferCache.buf` when the cached version equals
    `readTx.buf.bufVersion` (`backend.go:321-358`).
  - Only `writeback` bumps the version (`tx_buffer.go:114`). A commit empties the read buffer
    (`readTx.reset`, `read_tx.go:133-138`) and keeps the version (the batch's own
    `txReadBuffer.reset.spec` says "the version kept").
  - So after a run-loop or forced commit with no write-back since, a new concurrent read transaction
    lays the pre-commit buffer over the post-commit bbolt transaction.
- **Effects** (each reproduced: `nonissues/etcd-backend-read-buffer-cache-stale-after-commit.md`,
  test failing upstream):
  - a range of `Key` returns a key twice. `rdRange` is false: `sortedEnts` has no duplicates, and
    with `clean` set by `beCurIs_flush` the spec claims "bbolt's part only";
  - a cell a pre-commit hook rewrote at the commit reads its old value. This is false for every
    `F` holding a hook-written cell, including single-key reads and `UnsafeForEach`.
- The sketch's "the cache's invariant: a copy of the buffer at the version it records" is true but
  does not give "the buffer now".
- The old proof restricted exactly this: `keyReadSnap` with `rng = false`, the hook's buckets
  excluded.
- **Callers:**
  - 3e's contract: `rangeOk rt (kbRead B rt D) D KeyData.rtRange` holds for every `rt`, concurrent
    ones included, so the bridge would have to prove a false range row;
  - `ReqSeqRange`'s first read;
  - anyone tracking hook cells through a concurrent read.
- **Fix:** either of these.
  - **(a)** State the concurrent read transaction's reads as true of the code:
    - `concurrentReadTx.UnsafeRange` only with `es = slice.nil` (single key);
    - `UnsafeForEach` (which deduplicates against the buffer and is right for non-hook cells);
    - and only for footprints no pre-commit hook writes. That needs the hooks' footprint fixed at
      `New`: `hookOk γ hk Fh Pk`, and `ConcurrentReadTx` taking `⌜∀ c, F c → ¬ Fh c⌝`.

    3e's `rangeOk` for `rt ≠ kbReadTx B` then becomes single-key; mvcc's only concurrent read is
    single-key (`kvstore_txn.go:126`), and `hash.go:35` uses `UnsafeForEach`.
  - **(b)** Take the fork's one-line fix (`fix/etcd-backend-read-buffer-cache-stale-after-commit`:
    `bufVersion++` in `readTx.reset`) into the pinned fork and keep the general spec.

  (b) is a code change for the user to approve, and the branch keeps the current translations.
  Recommend (a) now, with (b) recorded as an open question.

### T2. The pre-commit hook's puts stay in the write buffer after the commit (spec claims too much)

- **Principle:** sound.
- **Targets:** `Api.lean` (`hookOk`, `hookFnOk`, `beCurIs_flush`), `readTx__UnsafeRange.lean`.
- **Mechanism:**
  - `unsafeCommit` runs `hooks.OnPreCommitUnsafe(t)` with `t` the `*batchTxBuffered`
    (`batch_tx.go:381-386`), so the hook's `UnsafePut` also appends to `t.buf`
    (`batch_tx.go:408-411`).
  - `batchTx.commit` then sets `pending = 0`, but nothing empties `t.buf`. Only `writeback` does, at
    the next `Unlock` with something pending.
  - At that point the hook's entries are already in bbolt's new read transaction, and the write-back
    puts them in the read buffer too.
- **Effects:**
  - For a hook that puts into a **safe-range** bucket (with a fresh key, as `hookOk` allows): every
    later read-transaction range of that bucket returns the key twice (bbolt's part, then the
    buffer's). `rdRange` is false.
  - For any bucket a hook writes: `beCurIs_flush` lets a client record the bucket clean at the commit
    point, and the leftovers then enter the read buffer at a write-back that does not clear the flag
    (`Sess.mid`'s `clean` clears only buckets the session itself put to). `clean` is consulted only
    for safe-range buckets, so the damage is confined to the first effect.
- etcd's hooks write only `Meta`, which is not safe-range. The old spec had "hook buckets" (`HB`,
  `specs-ref` `notes/backend-cmp-plan.md:140-152`).
- **Callers:** none in etcd today. The spec as written is unprovable for a hook any client may
  supply (`NewHooks.spec` takes any `f`).
- **Fix:**
  - In `hookOk`'s continuation, require the hook's session to have put to no safe-range bucket. For
    example `∀ bk bi, bucketOk bk bi -∗ ⌜bi.safe → ¬ S'.putIn bi.name⌝`, or a fixed hook footprint
    of non-safe cells, which T1(a) needs anyway.
  - Say in `Unlock`'s sketch that the write-back also flushes the last commit's hook leftovers, whose
    values equal the committed ones.

### T3. Bytes from bbolt are given "for good"; 4c lends them only while the transaction lives (unprovable)

- **Principle:** sound against the callee's specs.
- **Targets:** `readTx__UnsafeRange.lean`, `concurrentReadTx__UnsafeRange.lean`,
  `batchTxBuffered__UnsafeRange.lean`, the three `UnsafeForEach` specs (`visitOk`'s `ks ↦*□ k`),
  `bytesListAt`.
- **Evidence:**
  - Every range post gives `bytesListAt kl …`, that is `p ↦*□ b`, for keys and values bbolt's cursor
    returned.
  - 4c gives `txBytes tx γ s b`, "the slice `s` holds `b` while `tx` is live", readable only through
    `txBytes_acc` with `boltTx` (`SpecPlan/Spec/go_etcd_io/bbolt/Api.lean:196-198, 356-359`).
  - In Go these slices point into the mmap or the transaction's nodes. After the read transaction
    rolls back and a later write remaps, reading them faults.
- The author asked 4c for the lifetime (`req/go_etcd_io_bbolt.md`, "from 4a" item 5) but wrote the
  specs as if the answer were "forever". 4b has already moved to lent bytes ("from 4b, round 1",
  item 1).
- **Callers:**
  - mvcc's contract (`bytesListAt` in `rangeOk`): mvcc unmarshals inside the read
    (`kvstore_txn.go:126-131`);
  - `restore` passes the slices to a goroutine under the read lock (`kvstore.go:347`). Check that it
    finishes before `RUnlock`.
- **Fix:**
  - Lend the bbolt part against the transaction resource: a wand `beRd γ rt F V`-and-bytes back to
    `beRd`, or the session's.
  - The buffer's part (session puts, `ks ↦*□ k`) may stay persistent. A uniform lent result is
    simpler.
  - Ask 3e to restate `rangeOk` the same way.

### T4. Vocabulary with no introduction (every premise has a source)

- **Principle:** every premise has a source the client sees; complete.
- **Target:** `Api.lean`.
- **`bucketOk bk bi`** (opaque, persistent) is a premise of every read and write spec. No law
  introduces it.
  - 4a asks 4b for `Schema.bucketAt b bv ⊢ Backend.bucketOk …`, but `bucketOk` is 4a's opaque
    predicate: only 4a's realization can prove anything of it.
  - `bucketOk_id` (ids unique across all `bucketOk` facts) cannot be proved by a realization that is
    "the value's methods return these". The uniqueness is a fact of the schema's variables.
  - Fix:
    - make `bucketOk` transparent, the bundle of `ID()`, `Name()` (read-only name slice) and
      `IsSafeRangeBucket()` triples, which 4b proves of `bucketAt` (PRINCIPLES, "an interface value
      gets a bundle");
    - make the id uniqueness a premise the specs that need it take, or a 4b law over its `Bkt`
      values;
    - for `Defrag`, the safe-range registry's agreement with the flags (`isRegisteredSafeRangeBucket`
      by name) is also a 4b fact. Say so in `Defrag`'s comment and take it as a premise of the
      non-blocking mode.
- **`beFile p o`** has no law at all.
  - `New.spec` cannot be called: there is no `beFile p none` for a fresh path and no `beFile p
    (some I)` from a file on disk.
  - `OpenSnapshotBackend`'s rename (2e item 1, "a rename carries the image") has nothing to use.
  - Fix: laws from 4c's `fileHolds` (`fileHolds_new`, `fileHolds_image`), say `beFile_of_fileHolds`
    and a rename law, or `New` stated over `Bbolt.fileHolds path D` with `imgOf D`.
- **`envOk`**: no introduction. 2e's `backendEnvOk` is meant to be it.
  - Fix: `envOk_intro` from the program-start environment fact (`ETCD_VERIFY` unset) and whatever
    the thread accounting really needs (see S4).
- **No crash law.**
  - The header's "a crash leaves one of them" (`beHist`) is not stated anywhere. No client can turn
    `beHist γ L` into a `beFile p (some I)` with `I ∈ L` after a crash.
  - 2d item 3 ("a crash keeps the last commit's image") and 3c item 4 ("writes under one lock hold
    land in one commit … the crash image must keep them together") are unserved.
  - 4c has `boltCrash` (`SpecPlan/Spec/go_etcd_io/bbolt/Api.lean:102`) to build it from.
  - Fix: a `beCrash` law over `beHist`, gated by a recorded `UnsafeNoFsync` mode (Q3: record it in
    `isBackend`'s index or as a persistent `beSynced γ` from `New`).

### T5. The bridge `keyBackend_intro` (`MvccStorage.lean`)

The file does not build at HEAD:

```
MvccStorage.lean:92:14: error: Unknown identifier `Mvcc.bucketVal`
MvccStorage.lean:93:14: error: Unknown identifier `Mvcc.bucketVal`
```

3e round 2 replaced `bucketVal` by `Schema.bucketAt`. Its header ("Blocked on 3e's contract") and
`batch-4a.md`'s F1/F3 entries are stale: 3e has `kbLocked B D0 D`, the nested two-step `Unlock`,
and the freshness over `D0` and `D`.

I checked the rows against the decided fix. Realization: `kbData B D := ∃ V, beVis γ mvccFp V ∗
⌜D = keyDataOf V⌝`; `kbLocked` holding the session widened to `mvccFp` and `beCur γ mvccFp C`, with
`D0`/`D` read off `S.base`/`C` and `D.clean := S.base.clean key && !S.putIn key`.

- The **`Unlock` row** goes through: mvcc's nested update is the backend's two updates, with
  `Ψ1 := AU2`.
- The **put rows** go through modulo (c).
- **`LockInsideApply`/`LockOutsideApply`**: `kbObs` can fire after the lock with `beSess_vis`.
- **`kbObs`, `ConcurrentReadTx`, `RLock`/`RUnlock`, bare slots, `storageReq`/`storageHook`**: fine.

Remaining obstacles:

- **(a) Open shares.**
  - The backend's `LockInsideApply`, `LockOutsideApply` and `ForceCommit` take `beOpen γ q`. mvcc's
    rows take none, and the bridge has none in its premise or its way back.
  - They cannot live in `kbData` either: `Unlock` returns the share only in its post, after both
    updates fired.
  - `ForceCommit` after the close panics through the hook (see "What is good").
  - The batch's Q5 reaches this conclusion for 3c but not for 3e. Fix: an open token in 3e's
    contract (`kbOpen B q`, fractional, on the lock rows and `ForceCommit`, returned by
    `storageRest`), realized by `beOpen`.
- **(b) A put followed by a delete of the same key in one session.**
  - `keyDataOf (Sess.mid S)` shows the put value; 3e's `KeyData.mid D0 D` shows `D0`'s value, since
    `D.keys k = none`.
  - The Key delete row allows deleting any key. Fix in 3e: the delete row takes
    `⌜D.keys k = D0.keys k⌝` (the key was not put in the session; mvcc's compaction deletes only
    revisions from before), or `kbLocked` carries the session's puts.
- **(c) The entry bound.**
  - `UnsafePut`/`UnsafeSeqPut` take `k.length + v.length ≤ Bbolt.bboltEntryMax`. mvcc's `Key` put row
    and its `Meta` compaction-key row take none.
  - 3e must add it: mvcc's values are bounded by the server's request size, and the compaction keys
    are 17 bytes. This is the mvcc counterpart of F4.
- **(d)** `□ (Mvcc.kbHeld B ∗-∗ ∃ q F S, beSess γ q F S)`.
  - The ← direction gives a `kbHeld` from a session with any `F`. Rebuilding `kbLocked` from it
    leaves an `Unlock` that needs an update over `beVis γ F` for an `F` mvcc does not own, and there
    is no narrowing law.
  - Fix: pin `F := mvccFp`, or state only the lend
    (`kbHeld B ⊣⊢ ∃ q S, beSess γ q mvccFp S`).
- **(e)** T1: the range row on concurrent read transactions.
- **(f)** T3: bytes for good.
- **(g) The way back** (`storageRest … ={⊤}=∗ ∃ V', beVis γ mvccFp V' ∗ …`) drops `beCur γ mvccFp`
  and ties `V'` to nothing. `backend.Close`'s post does not relate the final image `I` to the
  trackers it took. So after the shutdown no one can learn what the closed file holds of mvcc's part
  (3e item 4; 2e's reopen, `memberDisk`).
  - Fix: `Close`'s post adds `⌜Image.agree F I V⌝`. This is true: after the last `Unlock` the
    visible entries are the batch's, and the final commit commits them, plus hook cells, which the
    caller must have untracked.
  - The way back returns `∃ D, … ⌜keyDataOf V' = D⌝` with the `D` of `storageRest`.

### T6. The post-lock hook's backend read has no source (user not served)

- **Principle:** complete.
- **Targets:** `batchTxBuffered__LockInsideApply.lean` (`hookRun`), `Api.lean`'s `beSess_rd`.
- **Evidence:**
  - The server's post-lock hook calls `consistIndex.UnsafeConsistentIndex()`
    (`server.go:2478-2484`).
  - On a fresh member (in-memory index 0) that reads `ReadTx()` without `RLock`
    (`cindex.go:102-110`).
  - `hookRun Pk f Pre Q` runs `f` from `Pk ∗ Pre` only. The session exists only in
    `LockInsideApply`'s post, after `f` ran, so `f` cannot use `beSess_rd`.
- 4a's answer to 4b's item 3 ("`beSess_rd`") therefore does not serve this, its main use.
- **Fix:** `hookRun` passes the session in and out:
  `□ ∀ Φ S, beSess γ q Fp.none S ∗ Pk ∗ Pre -∗ ▷ (beSess γ q Fp.none S ∗ Q -∗ Φ #()) -∗ WP f …`.
  - Mirror it in 3e's `hookRun` and 4b's `applyHook`.
  - Or lend `beRd γ (rtLoc γ) G V` for the caller's `beVis` through `Pre`, made by a
    `LockInsideApply` that holds the session while it runs `f`.

## Second tier

- **S1. The hook's session at a commit inside `Unlock`** (uncertain: depends on a linearization the
  sketch does not fix).
  - **The conflict:**
    - When `Unlock` commits after a deleting session, the readers' physical view during the hooks is
      `mid` (old bbolt read transaction plus buffer).
    - `hookOk` hands the hook a session with `⌜S.base.ents = S.cur.ents⌝`. That is provable only if
      the session's second update fires at `readTx.Lock` in `commit`, before the hooks.
    - But then `beSess_rd`, applied to the hook's session, lends a `beRd` at the visible image
      (`fin`), while `rt.UnsafeRange` physically still reads `mid`. A deleted key reads present.
  - **Fix:** say which linearization is used, and give the hook's session a predicate `beSess_rd`
    does not apply to. Alternatively, drop the `ents` premise and give the hook its honest base.
- **S2. Snippets.**
  - Each put-snippet (`ReqWriteThenRead`, `ReqDeleteVisible`, `ReqLentWrite`, `ReqReopen`,
    `ReqSeqRange`, `ReqMetaSingle`) lacks the entry bound in `Assumes`, and `openBackend` lacks
    `dbOpenOk`. They are unprovable as stated, and trivially fixed.
  - Every snippet needs `bucketOk` of `schema.*` (T4).
  - `ReqHookWrites` puts the hook's tracker "in the lock's resource Pk". The main thread's final
    `RLock` then cannot fire its update: `Pk` is inside the batch mutex's lock invariant, not an Iris
    invariant. Assume an invariant holding the tracker (the hook's update opens it).
  - `ReqForceCommitDurable` checks nothing. Make it observe the per-call step: a `beReq` whose `Y`
    is `beCommitted` of an image holding a write unlocked before, read back as in `ReqSeqRange`'s
    clean step.
  - `ReqSeqRange`'s header cites `hash.go` as "an unlimited range on a ConcurrentReadTx": it is
    `UnsafeForEach`.
- **S3. Uncovered patterns** (one snippet each would do):
  - `UnsafeForEach` on a read transaction and on the batch:
    - read transaction: `schema/alarm.go:93`, `membership.go:98`, `auth_users.go:87`, `hash.go:35`;
    - batch: `schema/lease.go:33` under `LockOutsideApply`.
  - The compaction batch: `LockForSafeRangeDelete`, `Key` deletes, then the `Meta`
    finished-compaction put in one session (`kvstore_compaction.go:31-71`: F1's case, with
    `beDelHeld`).
  - The batch transaction's limited range (`kvstore_compaction.go:58`).
  - The post-lock hook (`SetTxPostLockInsideApplyHook` then `LockInsideApply` with a non-nil hook,
    `server.go:409`; T6).
  - `Defrag` (`server.go:976`, `bootstrap.go:323`).
  - `Hash` (`kvstore.go:161`).
  - `Size`/`SizeInUse` after `Close` (2e's `beReadable`, `bootstrap.go:284`, `quota`).
  - `New` over a received snapshot file (`storage/backend.go:62-71`).
  - The shutdown handing every tracker to `Close` (the lessor's `beNoVis`, mvcc's `storageRest`, the
    hook cells untracked first: see T5(g)).
- **S4. The rollback goroutine's thread** (Q6).
  - "A handle on the thread pool" in `envOk` does not guarantee a token at each `go`: a pool lends
    tokens it holds, and commits are unbounded in number.
  - The old proof needed no pool: `wp_fork_tok_self` hands the rolled-back read transaction's token
    to the goroutine and keeps a fresh one for the new read transaction (`specs-ref`
    `Proof/.../batchTxBuffered__unsafeCommit.lean:171-177`, `notes/begin-tok-plan.md`). Adopt it
    and close Q6.
  - The goroutine outliving `Close` is then harmless: `DB.Close` waits for the read transaction's
    `mmaplock` share.
- **S5. Internal specs.**
  - **`bucketBuffer.merge` with an empty `src`** reads `bbsrc.buf[0]` (`tx_buffer.go:221`). That is
    an index panic if `src`'s slice has length 0, as a `CopyUsed` copy of an empty buffer has.
    Moreover:
    - `mergeOk`'s "every new key follows every old one" is not the code's test (old's last against
      new's first);
    - with `new = []` the code may `dedupe` the old buffer (a stale `buf[0]` key), where `mergeOk`
      says `res = old`.

    Add premises: `src` writable-capacity, `old` and `new` sorted.
  - **`bucketBuffer.add` on a `CopyUsed` copy** (`len(buf) = used`) panics at `buf[used]`.
    `CopyUsed.spec` returns the same `bbAt c l` that `add.spec` accepts. `bbAt` needs a capacity or
    "writable" index.
- **S6. `New`'s premises.**
  - `cfg.Mlock' = false` is 4c's scope restriction (D13). It excludes `--experimental-memory-mlock`
    (`storage/backend.go:55`); say so in `New`'s comment as a filed scope restriction.
  - `UnsafeNoFsync` (Q3): record the mode (T4, crash law).
- **S7. `Close` and the hooks' trackers.** The final `CommitAndStop` inside `Close` runs the hooks,
  whose update needs the trackers of the cells they publish. Those trackers are in `Close`'s
  precondition. The server must therefore untrack the hook cells (`beVis_drop`) before closing. Say
  it in `Close`'s comment (2e's `bootstrappedBackend.Close`, the shutdown).
- **S8. Smaller points.**
  - `Sess.mid`'s `made` is the batch's. Readers do not see a created, uncommitted bucket (bbolt's
    read transaction lacks it, `read_tx.go:107-113`), but no read spec exposes `made`. A margin
    note.
  - The laws `beReaderN_ge`/`beReaderN_mvcc` name slot counts in API statements. They follow 3e's
    `kbRdToks`; the bounds rule wants the count owned in one place. Note only.

## Callers' requests ("from" sections of `req/..._backend.md`)

| from | item | answered? |
|---|---|---|
| 2d | 1, 2 (`beStoredCI`, `txStoredCI`) | over `beVis`/`beCur` of `meta`'s cells: yes, modulo T6 (the post-lock hook's read) |
| 2d | 3 (commit image, crash) | commit step `commitOk`: yes; crash: **no** (T4) |
| 2d | 4 (`Snapshot`, `Size < 2^62`, `Close` nil) | yes |
| 2d | 5 (`VerifyBackendConsistency`) | yes (`envOk`, T4's intro missing) |
| 2e | 1 (`BeImage`, `emptyImage`, `beFile`, rename) | types yes; `beFile` laws **no** (T4) |
| 2e | 2 (`beOpen`, `beReadable`, `beTx`) | yes; the closed file's image vs the trackers **no** (T5g) |
| 2e | 3, round 1 (`backendBootRes`, quota ≤ 8 GiB) | `dbOpenOk` (opaque env premise): acceptable; `Mlock` (S6) |
| 3c | 1 (`beOk` persistent) | correctly refused (needs an open share); 3c must change |
| 3c | 2, 3 (`beHook`, `beTxHeld`) | yes (`beHook`, `beSess` lent); `hookRun` T6 |
| 3c | 4 (one commit per lock hold, crash) | per-session atomicity holds; crash law **no** (T4) |
| 3e | 1–5, round 2 | rows check out (above) but the bridge does not build and has T5a–g |
| 4b | 1–6 | the vocabulary yes; `bucketOk` intro **no** (T4); `applyHook`/item 3 **no** (T6); round 1's lent bytes **not yet** (T3) |

## The targets ranked by need of revision

1. **`MvccStorage.lean`**: does not build; T5a–g; stale header.
2. **The concurrent read side**: `backend__ConcurrentReadTx`, `concurrentReadTx__UnsafeRange`,
   `__UnsafeForEach` (T1, T3).
3. **`Api.lean`**:
   - no intro for `bucketOk`, `beFile`, `envOk`; no crash law (T4);
   - `hookOk`'s footprint (T1, T2);
   - `hookRun` (T6);
   - `beSess_rd` versus the hook's session (S1);
   - `bytesListAt`/`visitOk` (T3).
4. **`batchTxBuffered__LockInsideApply`** (T6), **`backend__Close`** (T5g, S7), **`New`** (T4, S6),
   the shared read transaction's and batch's range/`ForEach` specs (T3).
5. **Snippets** (S2, S3).
6. **Internal**: `bucketBuffer__merge`, `__add`, `__CopyUsed`, `bbAt` (S5).
7. **Trusted** (`Snapshot`, `snapshot.*`, `Hash`, `Defrag`, `VerifyBackendConsistency`, `Validate*`,
   `newBoltLoggerZap`): fine. `Defrag`'s safe-range-registry assumption should be stated (T4).
