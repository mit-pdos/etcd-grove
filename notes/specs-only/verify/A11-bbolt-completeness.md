# A11-bbolt, completeness (verification round, 2026-11-09)

Reviewer: completeness kind, independent. Scope: batch 4c (`SpecPlan/Spec/go_etcd_io/bbolt/`, its `errors/`
API, `examples/specreq/bbolt/`) and batch 4d (`SpecPlan/Spec/go_etcd_io/bbolt/internal/{common,freelist}/`,
`examples/specreq/bboltinternal/`). Users scanned: etcd's backend (`.lake/src/server/storage/backend/
{backend,batch_tx,read_tx}.go`, defrag, `Snapshot`/`WriteTo`, `Hash`), its specs
(`SpecPlan/Spec/go_etcd_io/etcd/server/v3/storage/backend/`, `Durable.lean`), `schema/version.go`, bbolt's
own calls into `common`/`freelist` (bbolt `743299d`), `examples/bbolt/bank`, `examples/axiomcx/bboltnan`,
`examples/osfs/bboltfs` (minibolt: no bbolt call). Kubernetes does not use bbolt.
The findings below were written before reading `batch-4c.md`, `batch-4d.md`, `open-questions.md`
and `integration-*.md`; those were read afterwards only to mark what was already recorded.

## Verdicts

| batch | verdict |
|---|---|
| **4c** (bbolt public API, internals, `errors`) | **FAIL**: F1-F4 below (and F5, a caller's spec that 4c's does not support). Otherwise it closes, except where the open decision 4c-D1 (the sector rule, needed by `boltCrash` and so by `ReqCrashAtomicDurable`) is pending. |
| **4d** (`internal/common`, `internal/freelist`) | **PASS**. Every call bbolt makes into `common`/`freelist` has a spec and a snippet pattern. The bbolt-side premises are discharged by `Internal.lean`'s "freelist's side" and `txPage`'s realization. Open item 4.8 (D1/D3/D4) asks the user to confirm choices; nothing waits on it. |

## Counts

- Specs: 295 files in the area (149 in `bbolt/`, 91 in `common/`, 54 in `freelist/`, plus `errors/Api`).
  I checked the 53 public 4c specs and the laws against their users. For internals and 4d I checked
  the internal call patterns (names exist; the snippets cover each pattern). The other 4c
  internals were checked by name and user only: they mirror the code and the provability reviewer
  covers them.
- Snippets: 24 (`bbolt/`: 11; `bboltinternal/`: 13). 20 close as far as completeness goes. These
  do not: `ReqDefrag` (F1, F2, F3), and `ReqBackendRead`/`ReqBackendBatch`, which close but leave
  F4's pattern uncovered. One pattern has no snippet (S1).
- Users: about 75 call sites. They are 60 in the backend (12 patterns below), 14 in the bank,
  bboltnan and schema, and every `common.*`/`freelist` call in bbolt's `db.go`, `tx.go`,
  `node.go`, `bucket.go` and `cursor.go`. All 12 backend patterns are served except 4 (F4),
  9-10 (F1-F3) and 6 (F5, on the caller's side).
- Coverage against `specs-ref`: every old function spec has one here. I mapped `_r/_w/_kv/...`
  variants to one file. The 98 old `common`/`freelist` files are all present, and 4d adds
  `Copyall`, `Count`, `Freed` and `Pages`/`Pgids` `Len/Less/Swap`. Two old files have no
  counterpart, and both are vocabulary, not functions: `Data.lean` moved to `Model.lean`, and
  `Logger.lean` moved to `Api.lean`'s `boltLogger`, with `DB__Logger.lean`.

## Backend usage patterns (checked at a real call site each)

1. Open with etcd's options (`backend.go:216-237`). Served by `Open.spec`, `Options.lean`,
   `boltLogger` (zap) and `ReqBackendOpen`.
2. Batch write transaction (`batch_tx.go:137-246, 291-296`): `CreateBucketIfNotExists`, `Bucket`,
   `FillPercent=0.9` (`boltTx_fill`), `Put` (the persistent value as a `putLoan` at `□`),
   `Seek`/`Next`, `Delete`, `DeleteBucket` with `ErrBucketNotFound`, `Commit` with its two updates,
   then `Stats` after `Commit` (`txDone`). Served by `ReqBackendBatch` and `ReqDeleteBucketNotFound`.
3. Shared read transaction (`read_tx.go:95-118`): the bucket handle cached and shared, a cursor per
   goroutine at fractions of `boltTx` (`Tx.Bucket` on a read transaction at any fraction; the
   child cache is not written for read transactions). Served by `ReqBackendRead`. Its rollback runs
   on a forked goroutine after `txWg` (`batch_tx.go:391-396`): it needs `boltTx 1 ∗ txLive 1` after
   the wait and returns `threadTok`. Served.
4. **`backend.begin(write)` (`backend.go:1086-1098`)**: `Size`, `DB`, `db.Stats()`, `Info()` right
   after `Begin`. Read: served (`statSlot (some (tx,T))`). **Write: not served (F4).**
5. Compaction's delete of keys the same write transaction returned (`kvstore_compaction.go:58-71`,
   through `UnsafeRange`/`UnsafeDelete`). Served by `txLive`/`txBytes_acc` (`Bucket.Delete` takes the
   key's points-to read against a `txLive` share; inodes are not written in place). No snippet (S1).
6. `Snapshot` + `WriteTo` + `Size` + `Close` (`backend.go:381-424, 1124-1133`). Served on the bbolt
   side (`ReqSnapshot`). **The backend's trusted spec claims more than 4c gives (F5).**
7. `Hash` (`backend.go:425-452`): `View`, the root cursor, `Tx.Bucket(next)` with `next` read
   through `txLive`, `ForEach`. Served by `ReqHash`.
8. Close (`backend.go:486`) and Begin errors made fatal: served (`boltOpened_closed`,
   `dbBroken_state`).
9. **Defrag copy** (`defragdb` `:796-856`, `defragdbAndTrackLastKeys` `:862-951`, `catchUpDefrag`
   `:960-1033`): `ForEach`/`Seek`+`Next` on the source, `CreateBucketIfNotExists`/`Put` into the
   copy, commits interleaved, then the source's rollback. **Not served (F1).** Value loans and
   commit order are fine on the success path, as `ReqDefrag` shows.
10. **Defrag setup and swap** (`createDefragTmpDB` `:512-546`, `finishDefrag` `:565-606`,
    `cleanupTmpDB` `:553-560`): custom `OpenFile`, `NoSync`, `Sync`, double `Close`, then
    `os.Rename(tdbp, dbp)`, `os.RemoveAll(tdbp)`, and `Open(dbp)`. **Not served (F2, F3).**
11. Crash and restart (`Durable.lean`'s `beCrash` from `boltCrash`, `beFile_of` from `fileHolds`):
    the names exist and the premises fit (`beSynced` gives `σ.dur = some _`). The pending items are
    the backend's own recorded binder gap and 4c-D1.
12. `schema.ReadStorageVersionFromSnapshot` (`schema/version.go:48`): `Tx.Bucket(...).Get(...)` on
    a read transaction. Served (used only by etcdutl).

## First-tier findings

### F1. No law bounds the sizes of data bbolt holds, so a copy cannot call `Put` (4c)
- **Principle:** every premise has a source the caller sees.
- **Evidence:**
  - `Bucket.Put.spec` (`Bucket__Put.lean:49`) requires `kb.length + vb.length ≤ bboltEntryMax`.
  - `Tx.CreateBucketIfNotExists.spec` and `Bucket.CreateBucketIfNotExists.spec` require
    `kb.length ≤ maxKeySize`. Go does not check that one (`bucket.go` ~`:218-251`), hence the
    premise.
  - `Put` returns `ErrKeyTooLarge` when `maxKeySize < kb.length`, and defrag treats any error as
    a failure.
  - What a reader gets back (`curAt`, `Bucket.Get`, `ForEach`) carries no size fact. `Ent.wf`
    (`Model.lean:136`) is only "keys non-empty and sorted". `boltTx_wf` and `boltImage_wf` give
    only `wf`. The bounds appear in `fileHolds`' docstring (`Api.lean:86-87`) but not in any law.
- **Affected callers:** etcd's three defrag copies call `tmptx.CreateBucketIfNotExists(next)` and
  `tmpb.Put(k, v)` (`backend.go:827/849`, `905/930`, `1012/1020/1026`), and `ReqDefrag`'s
  `b.ForEach(func(k, v) { return tmpb.Put(k, v) })`. These callers hold `k` and `v` only as
  `txBytes` of another transaction. The backend cannot carry the bound itself across a snapshot
  restore: `fileHolds_image` with `boltImage` exposes only `wf`.
- **The error path makes it worse:** `defragdb` registers its defers so that `tx.Rollback()`
  (`:816`) runs before `tmptx.Rollback()` (`:805-809`). An unexcluded `Put` error therefore needs
  `txLive tx 1` back while the live `tmptx` still holds `putLoan`s of that transaction's bytes.
  `putLoan_done` needs `txDone tmptx`, which only arrives after that `Rollback`, so the proof is
  stuck.
- **Fix:** strengthen `Ent.wf`'s bucket case (or add `Ent.sized` to `boltTx_wf`/`boltImage_wf`):
  every key is at most `maxKeySize`, and a value entry's `key.length + value.length` is at most
  `bboltEntryMax`, recursively. This is true of bbolt: `Put` refuses large keys and has the entry
  premise, `CreateBucket` has the name premise, `fileHolds` is well-formed as its docstring says,
  and an image is a `WriteTo` of such a state. Add to `ReqDefrag`'s `Specs:` the law it then uses.
- **Already recorded?** Only the premise itself (D4, open question 4.9). The missing law to discharge
  it for read data is not recorded.

### F2. `openFileOk` is persistent, so etcd's one-file closure cannot meet it (4c)
- **Evidence:** `Api.lean:311-317`: `openFileOk f path := □ ∀ flag mode Φ, ▷(… osFileOf fl fd ∗
  osFd fd (DFrac.own 1) … ) -∗ WP f path flag mode {{Φ}}`. Every call must hand out an exclusive
  `osFileOf`/`osFd`. etcd's closure (`backend.go:522-527`) returns the one `temp` file it created,
  with a nil error, on every call. Its owner can produce those resources once, never under `□`.
  bbolt calls `openFile` exactly once (`db.go:243`), so the `□` buys nothing.
- **Affected callers:** `createDefragTmpDB`'s `bolt.Open(tdbp, 0o600, &options)` (`:534`).
  `ReqDefrag`'s Assumes ("openFileOk from its osFileOf and fd") is unprovable as stated.
- **Second part (uncertain, because `osFileOf` is provisional):** on `Open`'s error, etcd calls
  `temp.Close()` and `os.Remove(temp.Name())` (`:536-538`). `Open.spec`'s error disjunct gives back
  only `boltClosed γ`, not the file the contract lent. `ReqDefrag` returns on that error without
  touching `tmp`, so the pattern is uncovered.
- **Fix:**
  - Make the contract one-shot: drop `□` and keep it a plain wand in `Open`'s premise.
  - Have `Open`'s error disjunct return what the caller needs to `Close`/`Name` the file (the
    `osFileOf fl fd`, now closed, or a share of it).
  - Extend `ReqDefrag` with that error path.
- **Recorded?** No. I7 records only that `osFileOf` is provisional.

### F3. No law releases a closed database's file from `boltFile γ`, so defrag cannot rename or remove it (4c)
- **Evidence:**
  - `boltFile γ` is a persistent crash invariant that holds the file's OsFs resources while the
    database is closed (`Api.lean:33-44`).
  - `DB.Close.spec` returns only `boltClosed γ`.
  - No law turns `boltClosed γ ∗ boltState γ 1 σ` (with `boltFile γ`) back into `fileHolds
    γ.path σ.data` or into the raw `osMeta`/`osBytes`. The laws are listed at `Api.lean:116-125`;
    the only file laws are `fileHolds_new`, `fileHolds_image`, `fileHolds_alloc` and `boltCrash`.
- **Affected callers:**
  - `finishDefrag` (`backend.go:570-594`) closes `odb` and `tmpdb`, then calls `os.Rename(tdbp,
    dbp)`. That needs the full OsFs resources of both paths, which are locked in `boltFile
    γ_old`/`boltFile γ_tmp`. It then calls `bolt.Open(dbp)` under a new name, which needs
    `fileHolds dbp D` for `fileHolds_alloc`.
  - `cleanupTmpDB`'s `os.RemoveAll(tdbp)` (`:557`) has the same problem.
  - `ReqDefrag` says it covers `finishDefrag` (`:565-620`), but it reopens `odb`'s own path under
    the same name and never renames. The aspect etcd relies on (swap the synced copy in) is not
    captured.
- **Fix:** add a release law. One shape:
  `boltFile γ ∗ boltClosed γ ∗ boltState γ 1 σ ⊢ |={E}=> (⌜σ.dur = some [] ∧ σ.busy = false⌝ -∗
  fileHolds γ.path σ.data) ∧ (∃ mo, osMeta γ.path 1 mo ∗ …)`. Realization: a cancelable crash
  invariant whose token is in `boltClosed`; after `tmpdb.Sync()`, `σ.dur = some []`. Then extend
  `ReqDefrag` to sync, close both, rename (OsFs's `rename` once it exists) and reopen through
  `fileHolds_alloc`. The same law serves `cleanupTmpDB`.
- **Recorded?** Partly. `batch-4c.md` "Needs of others" and I7 item 6 record "OsFs has no `rename`,
  defrag/restore not expressible yet". The missing bbolt law is a separate gap: even with OsFs's
  `rename`, the resources stay inside `boltFile`. (Related, 2e's: `applySnapshot` renames a
  snapshot file over the path of a backend that is still open.)

### F4. `DB.Stats` after `Begin(true)` has no reader slot to pay with (4c and its caller, 4a)
- **Evidence:**
  - `statSlot` (`Api.lean:351-354`) is either `threadTok` or the whole of a read transaction
    (`⌜T.rw = false⌝`).
  - `backend.begin(true)` (`backend.go:1086-1098`) calls `db.Stats()` holding only the write
    transaction. It runs on every batch commit (`batch_tx.go:318`) and from `newBatchTxBuffered`.
  - `backend.begin.spec` (`backend__begin.lean`) has no `threadTok` in its premise. Its sketch does
    not mention `Stats` or `Info` at all.
  - The old backend used `DB.Stats_kv` (`specs-ref/Spec/go_etcd_io/bbolt/DB__Stats_kv.lean`), with
    no slot, so this tension is new.
  - No snippet calls `Stats` with a write transaction live.
- **Fix:**
  - In 4c (local, preferred): let `statSlot (some (tx,T))` accept a write transaction's whole
    `boltTx`. The writer holds `rwlock`, so one spare `statlock` reader slot in `isBolt` suffices,
    as `freepages` already has one spare `mmaplock` slot.
  - Or in 4a: thread the committing thread's `threadTok` through `begin(true)`'s premise, up to
    every `Unlock`/`Commit` caller.
  - Add `d.Stats()` after `Begin(true)` to `ReqBackendBatch`.
  - In passing: `backend.begin.spec` is stated only at `#true`. `begin(false)`
    (`batch_tx.go:405`) has no spec instance.
- **Recorded?** No.

### F5. The backend's trusted `snapshot.WriteTo` fixes the bytes, but `Tx.WriteTo` does not (the caller's spec; 4a)
- **Evidence:**
  - `backend__Snapshot.lean:52` returns `beSnap γ s I bs` with `bs` fixed at `Snapshot()`.
  - `snapshot.WriteTo.spec` (`snapshot__WriteTo.lean:38-44`) writes exactly that `bs` and gives
    `beSnap` back for further calls.
  - `Tx.WriteTo.spec` gives a fresh `∃ img, boltImage img T.base ∧ img.length = sz` on each call.
    That is right for Go: the pages read are `[2, hwm)` from the file, and free pages below the
    high-water mark can be reallocated and rewritten by a concurrent commit while the reader is live.
  - So the trusted spec's "why it is true" ("4c's `Tx.WriteTo`") does not follow from 4c. A second
    `WriteTo` of one snapshot can produce different bytes.
- **Fix (in 4a, not 4c):** `beSnap γ s I n` carries the size, and each `WriteTo` writes some `bs`
  with `imgBytes I bs ∧ bs.length = n`. `snapshot.Size` then returns `n`. 2d's receiver needs only
  the image and its length.
- **Recorded?** No. I4, X and Y discuss `beSnap`'s realization, not this.

## Second-tier

- **S1.** No snippet for "delete a key the same write transaction returned" (pattern 5, the reason
  `txLive` exists, integration Y). The spec serves it. Add `ReqDeleteReturned`:
  `Seek`/`Next` collect keys, then `b.Delete(k)` for each, with a panic if a later returned key's
  bytes changed or if one is still there.
- **S2.** `ReqDefrag` has a single copy loop. The non-blocking variant (`catchUpDefrag`: `Seek` from
  a stored last key, commits and `Begin(true)` interleaved within the source cursor's iteration, a
  `Sync` while further commits follow) is not shown. The specs serve it, given F1. Optional.
- **S3.** `ReqDefrag`'s Assumes should say what excludes `defragdb`'s error paths while `tmptx` is
  live (see F1's ordering note): the root holds only buckets, and the entries are bounded (F1's law).
- **S4. Code reading, nonissue candidate (not filed: this review is read-only).**
  `defragdb`/`defragdbAndTrackLastKeys` reassign `tmptx, reopenErr = tmpdb.Begin(true)`. On error
  `tmptx` is nil, and the deferred `tmptx.Rollback()` (`backend.go:805-809`, `:869-877`) then
  dereferences nil (`tx.go:304`, `tx.managed`). It is unreachable in etcd: `Begin(true)` fails
  only if the database is closed or its mapping was lost by a failed commit, and the previous commit
  succeeded. This is the shape `nonissues/` records (a precondition etcd meets);
  `blocks-proof: no` (`dbBroken_state` with a successful commit excludes it). Not found in
  `issues/` or `nonissues/`.

## What is good

- Durability is part of the client-owned state (`BoltSt`: commit, attempt, settle, sync), with two
  updates per commit that fire on every path. The bank's atomicity and durability snippet follows
  from them (pending 4c-D1).
- `putLoan` (a value lent until the transaction is done) and `txLive` (byte validity separate from
  `boltTx`) fit etcd's two hard cases: defrag's cross-database copy on the success path, and
  compaction deleting the keys it read.
- Errors are disjuncts, not premises: read-transaction mutations, `ErrBucketNotFound`,
  `ErrTxClosed` on defrag's deferred `Rollback`, and `Begin`'s `dbClosed ∨ dbBroken`, which callers
  exclude through laws.
- 4d's freelist contracts carry the premises of the real panics, and `Internal.lean` says where
  bbolt's realization discharges each one. The internal snippets cover every pattern of bbolt's
  calls into `common`/`freelist` (node, meta and freelist-page round trips, element reads, the
  release rule, alloc/free/rollback, reload with empty ids, `WriteTo`'s metas, the sort before
  write).

## Targets ranked by need of revision

1. `Api.lean`: `openFileOk` (F2), the release law (F3), `statSlot` (F4), and `Model.lean`'s
   `Ent.wf` or a new size law (F1).
2. `examples/specreq/bbolt/backend.go`'s `ReqDefrag`, which needs F1-F3 and S2-S3.
3. `Open.lean`'s error disjunct (F2, second part).
4. The backend's `backend__begin.lean` (F4), `snapshot__WriteTo.lean`, `snapshot__Size.lean` and
   `backend__Snapshot.lean` (F5): another area's files, findings for its author.
5. A snippet for compaction's delete (S1).
6. 4d: nothing.
