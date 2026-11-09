# Batch 4c: bbolt's public API (DB, Tx, Bucket, Cursor)

Author's report, round 0 (2026-11-09). Namespace `Bbolt` (`Perennial.EtcdGrove.Bbolt`).
Build: `etc/specs-build.sh --dir Spec/go_etcd_io/bbolt`: OK, 149 modules (round 1).

## Files

`Spec/go_etcd_io/bbolt/`:

* `Model.lean` (pure, transparent): `Ent`/`Data` (nested buckets: a value or a bucket with its
  sequence and sorted entries; a database is its root bucket), `BPath`, the operations (`lookup`,
  `atPath`, `bktAt`, `insEnt`, `delEnt`, `setKey`, `setSeq`, `modAt`, `curEnts`, `seekIdx`),
  `TxView` (`rw`, `managed`, `base`, `cur`, per-path `gen`, `noSync`; `ro`, `wr`, `gens`, `ents`,
  `setCur`, `dropBkt`), **`BoltSt`** (the client-owned state: `data`, `dur`, `busy`, `lost`;
  `init`, `recovers`, `commit`, `attempt`, `sync`, `settle`), the bounds (`maxKeySize`,
  `maxValueSize`, `bboltEntryMax`, `float64IsNaN`), `OptsM` (`dflt`, `ok`, `loggerPtrOk`).
* `Api.lean`: the vocabulary and laws (below).
* `Internal.lean`: `CommitStage`, `wtxAt` (internal: the commit path's stages).
* Public API (45): `Open`; `DB__{Close,Begin,View,Update,Sync,Stats,Info,Path}`;
  `Tx__{ID,DB,Size,Writable,Cursor,Stats,Bucket,CreateBucket,CreateBucketIfNotExists,DeleteBucket,
  ForEach,Commit,Rollback,WriteTo}`; `Bucket__{Tx,Writable,Cursor,Bucket,CreateBucket,
  CreateBucketIfNotExists,DeleteBucket,Get,Put,Delete,Sequence,SetSequence,NextSequence,ForEach,
  ForEachBucket}`; `Cursor__{Bucket,First,Last,Next,Prev,Seek,Delete}`.
* Internal (6, mirror the code): `Bucket__rebalance`, `Bucket__spill`, `Tx__commitFreelist`,
  `Tx__write`, `Tx__writeMeta` (the commit point), `cloneBytes`.

`examples/specreq/bbolt/` (`go vet` clean): `backend.go` (`ReqBackendOpen`, `ReqBackendBatch`,
`ReqBackendRead`, `ReqDeleteBucketNotFound`, `ReqHash`, `ReqSnapshot`, `ReqDefrag`), `bank.go`
(`ReqCrashAtomicDurable`: atomicity and durability across crashes, the bank test's claim),
`nested.go` (`ReqNested`, `ReqReadOnlyPut`, `ReqCursorDelete`).

## Vocabulary (`Api.lean`)

Every predicate takes `[HasExt osFsExt]` and the generation's `[hG : HeapGS HasLC.hasLC GF]` in its
own signature (the crash law relates two generations; an opaque body drops unused section
variables).

* `BoltName` (opaque), `γ.ns`, `γ.path` (opaque projections): one database file for one
  generation, across `Open`/`Close`.
* `boltState γ q σ` (fractional, timeless): the client-owned state (`BoltSt`); bbolt changes it only
  by the client's atomic updates.
* `boltFile γ` (persistent): the file's crash invariant (every crash image is a bbolt file whose
  data `σ.recovers`).
* `boltClosed γ` (exclusive): the file is closed; the right to `Open`.
* `isBolt db γ ns` (persistent): an open `*DB` with `NoSync = ns`.
* `boltOpened db γ` (exclusive): the right to close `db` (it stays open while held);
  `dbClosed db` (persistent): `db` was closed.
* `boltTx tx γ q T` (fractional); `txDB tx db`, `txDone tx` (persistent).
* `bktH tx γ b p gs` (persistent): a bucket handle at path `p`, current while `T.gens p = gs`.
* `boltCur tx γ c p gs T pos` (exclusive): a cursor, last positioned at view `T`.
* `txBytes tx γ s b` (persistent): a returned key/value slice.
* `fileHolds path D` (exclusive, timeless): a closed, fully durable database file holding `D`
  (what a generation starts from).
* `optsAt l dq o`, `optsArg l dq o` (nil options allowed); contracts `boltLogger l`,
  `openFileOk f path` (opaque), `writerOk w W` (transparent, over `writerPlain`), `boltImage bs D`
  (opaque `Prop`); `errIs g e`, `isErr g e`; `curAt`, `statSlot`.

**Laws**: `persistent`, `timeless`, `boltState_frac` (fractional, agree, valid), `excl`,
`boltTx_later`, `boltTx_frac` (+ agree, valid, nonnull), `boltTx_base`, `bktH_live`,
`txBytes_acc`, `boltTx_fill`, `boltState_read_au`, `boltState_commit_au`, `boltState_settle_au`,
`fileHolds_new`, `fileHolds_image`, `fileHolds_alloc`, **`boltCrash`** (the crash law),
`boltLogger_nil`, `errIs_init`, `errIs_distinct`.

## The durability design (what survives a crash, what `Open` recovers)

* The client owns `σ : BoltSt`: `data` (what a transaction beginning now reads) and `dur` (what a
  crash may recover besides `data`; `none`: no promise, after a `NoSync` commit not yet synced),
  with `busy` (a commit's meta write may be in flight) and `lost` (an `fdatasync` failed in this
  generation; Linux may have dropped dirty pages: OsFs's D2).
* `Commit` takes **two updates**: the commit update, fired at the first step of the meta page's
  `pwrite` (one aligned OS page, D9: all or nothing in-process) with the write's outcome known by a
  prophecy (`ok`: `σ.commit T.cur`, the old data stays recoverable; else `σ.attempt T.cur`: the
  data unchanged, but a crash during the write may find the new meta); and the settling update at
  the end (`σ.settle synced failed`: after the meta's `fdatasync`, only the new data is
  recoverable unless a sync failed before). `DB.Sync` takes a sync update (`σ.sync ok`).
* **The crash law** (`boltCrash.spec`): from `boltFile γ` and any fraction of `boltState γ q σ`
  with `σ.dur = some ds`, after `crashed`, the next generation takes `fileHolds γ.path D` with
  `σ.recovers D` out of OsFs's `crashRest`. `fileHolds_alloc` names it again (`BoltSt.init D`).
  `ReqCrashAtomicDurable` is the client's use (the bank: no torn transfer, no lost acknowledged
  transfer).
* `Open` recovers the page cache's data, which at a generation's start is the durable image:
  `σ.data` of the allocated state. It no longer consumes the file (`boltClosed` comes back on an
  error) or produces the state (`boltState` lives across opens).

## Changes from the old specs (`specs-ref/Spec/go_etcd_io/bbolt/`, frozen 2026-11-03)

* **Relaxed**: nested buckets (the old `Data` was top-level buckets only); mutations on read
  transactions (now `ErrTxNotWritable`, was a premise `T.rw`); `ErrIncompatibleValue` on a
  bucket's key; `nil` options; a custom `OpenFile` (etcd's defrag, the old round-6 margin);
  `NoSync` (a mode: `TxView.noSync`, `BoltSt.commit`); cursors repositioned after a change
  (`First`/`Last`/`Seek` at the current view); the closed file given back by `Close` (old D9); a
  second `Close`; `DeleteBucket("")` stated exactly.
* **New**: `View`, `Update`, `Sync`, `Path`, `ForEach` (`Tx`, `Bucket`, `ForEachBucket`), `WriteTo`,
  `Sequence`/`SetSequence`/`NextSequence`, `Cursor.Delete`, `Cursor.Bucket`, `Tx.ID`,
  `Tx.Writable`, `Bucket.Tx`, `Bucket.Writable`, error identities (`isErr`).
* **Restated**: client-owned `boltState` over `BoltSt` (was `Data`); `Commit`'s single update is
  now the commit update with an outcome plus the settling update; the handle generation is per
  path (`gens`); `Tx.Size` bounded below `2 ^ 48` (2d's need).
* **Dropped**: the `_kv` trust-boundary layers (one spec per function), the `_r`/`_w` mode
  splits, `dbCloseOk`, the old `fileHolds path D` consumed by `Open`.
* **Kept** (the user's decisions): D1 (`threadTok` reader slots, `statSlot`), D3 (bounds `2^29`
  threads, `2^62` receipts on `Open`), D4 (`bboltEntryMax`), D5 (`FillPercent` non-NaN), D7
  (client-owned state reached by updates), D13 (scope: read-write, default page size, `Mlock` off,
  `MmapFlags` `0`/`MAP_POPULATE`), D17 (`splitThreshold`), D18 (`getPageSize`), D20′ (the logger
  contract, now opaque `boltLogger`), D21 (`WriteTo`'s meta parity), D22 (OsFs's aligned-page
  `pwrite` rule); `Prev` on read transactions only (`issues/bbolt-cursor-prev-empty-leaf.md`).

## Left out

* Public, no user (etcd, the examples, the repository's tests): `DB.Batch`, `Tx.OnCommit`,
  `Tx.Copy` (deprecated wrapper of `WriteTo`), `Tx.CopyFile`, `Tx.Check`, `Tx.Inspect`, `Tx.Page`,
  `Tx.MoveBucket`, `Bucket.MoveBucket`, `Bucket.Inspect`, `Bucket.Stats`, `Bucket.Root`, `Compact`,
  `DB.Logger`, `DB.IsReadOnly`, `DB.String`/`GoString`, `Stats.Sub`, `TxStats`'s getters and
  `Sub`, `BucketStats.Add`, the loggers (`DefaultLogger`, the discard logger).
* Internal functions: none left out since round 1 (C8: every package-`bbolt` function with a
  proved spec in the old tree has one).

## Decisions for the user (in plain terms first)

**4c-D1. What a crash leaves of the meta page (round 1: restated).** bbolt keeps two copies of
its table of contents (the meta page: 80 bytes at the start of a 4 KiB page, with a checksum); each
commit overwrites the older copy and, in sync mode, syncs before and after. OsFs's crash model
(`CrashImage`, its D1) says every byte not known to be on disk is *arbitrary* after a crash. Then a
crash during or after a commit's meta write may leave in that slot any 80 bytes, **including a meta
with a correctly computed checksum** describing a state that never existed (a higher txid, a root
at a page of user bytes): no checksum collision is even needed. bbolt would open it and return wrong
data or panic, so `boltCrash.spec` is false under OsFs as it is. D22 does not help: it makes a
one-page `pwrite` all or nothing in the page cache (in-process), not in a crash image.
What bbolt actually relies on is narrower and physical: **a write of a page that is clean and idle
(not dirty, no writeback in flight) reaches the disk sector-atomically**: after a crash each of
its 512-byte sectors holds either its old durable bytes or the bytes that write gave it. The meta
lies in the page's first sector (4d's `BboltCommon.meta_in_sector.spec`: header 16 + meta 64 ≤ 512),
and in sync mode the meta page is clean and idle when bbolt writes it (it was last written two
commits ago and synced then, and `tx.write`'s `fdatasync` just waited for every writeback). The
general rule "each sector holds its durable bytes or some version the page cache held" is **false**
(Linux copies into a page under writeback without waiting unless the device needs stable pages, so a
sector can reach the disk half old, half new: reachable under `NoSync`, where bbolt promises nothing
anyway). Options:
- **(a)** add the narrow rule to OsFs's crash relation (for a sector changed by at most one `pwrite`
  since the file's last successful sync, finished or in flight: its durable bytes or that write's),
  with the kernel argument in `Impl.lean` as D22's is (from `mm/filemap.c`, `folio_wait_stable`;
  uncertain to that degree): the physical fact, every OsFs client benefits;
- **(b)** a crash premise visible in every bbolt closed theorem (`CrashP1.lean`'s `osFsSemWith Q`, as
  minibolt's P1): no kernel argument, but a premise in every statement.
`boltCrash.spec` is true under (a) or (b). **The user's decision.**

**4c-D2. A prophecy on the meta write (round 1: resolved on "the page was written").** The commit
update must fire when the meta write *starts* (a crash during it may already find the new meta);
whether the commit takes effect is known only when it *ends*. The proof needs a prophecy, resolved
before `metalock.Unlock` on **whether the page was written** (the mapped meta page's txid is the
new one), **not on `err == nil`**: OsFs's one-page `pwrite` may write the page and report an errno,
and `File.WriteAt` retries on `EINTR`, so a first attempt can write the page and a retry fail; the
meta is then current (`rollback` keeps it) with `err ≠ nil`, which the settling update records as
`failed`. A prophecy patch in `etc/proph-patches/bbolt/` (CLAUDE.md allows it; `etc/prophcheck` must
admit the read of the mapped meta page's txid, not checked here). Alternative: a third update.

**4c-D3. The durable state in the client's state, three updates.** `BoltSt` carries `dur`, `busy`
and `lost` so that a crash-safe client learns exactly what it may find after a crash, and a client
that does not care uses `boltState_commit_au`/`boltState_settle_au` and reads only `σ.data`. The
alternatives considered: a bbolt-owned monotone "synced" witness (cannot be invalidated by a later
`NoSync` commit, unsound in that mode); a synced flag fired at the meta's sync (a concurrent
`DB.Sync` could claim the in-flight meta durable: `busy` exists for that); never clearing `lost` is
conservative (sound; a client stopping at the first error, as the bank test does, never sees it).

**4c-D4. Names per file and generation.** `fileHolds_alloc` names a file once per generation;
`Open`/`Close` move the closed token; the state lives across opens (a defrag reopen keeps it). A
`Close` without the close right is allowed only on a closed database (`dbClosed`, the defrag's
second close).

**4c-Q5. The internal specs (round 1: done).** Every package-`bbolt` function with a proved spec in
the old tree now has one (review C8's list, 94), mirroring the code over `Internal.lean`'s model.

**Scope restrictions kept** (each a premise the code does not check, filed): read-write open, default
page size, `Mlock` off, `MmapFlags` (D13); bucket names within `MaxKeySize`
(`nonissues/bbolt-bucket-name-length-unchecked.md`); entries within `bboltEntryMax` (D4); `Prev` on
read transactions; `WriteTo` with a writer without `ReadFrom` (`writerPlain`: `io.Copy` would call
it; etcd's pipe has none).

## Needs of others (not a batch's `req/`)

* **OsFs** (this repository's extension): 4c-D1's sector rule; `os.OpenFile`'s spec over OsFs (the
  old `Spec/os/`, gone on this branch) for `Open`; `Fdatasync`'s and `pwrite`'s (D9) as they are.
  OsFs has no `rename`: the backend's defrag and snapshot restore (`os.Rename` over the database)
  are not expressible yet (4a's and 2e's).
* **Perennial's `io`**: `io.NewSectionReader`, `io.CopyN` (`Tx.WriteTo`), and `(*os.File).ReadAt`
  through them.
* **Batch 4d**: `req/go_etcd_io_bbolt_internal_common.md` and `..._freelist.md`, "from 4c" (meta
  round trip within the first sector, node/page round trips, element reads, chunked writes, image
  decoding; readers' registration, the release rule, allocate/free/rollback, the freelist page,
  counts, the id bound).
* **`bbolt/errors`** (no batch): answered 4d's request in this API (`errIs_init`,
  `errIs_distinct`; `req/go_etcd_io_bbolt_errors.md`, "from 4c (answer)").
* **Batch 4a** (backend): no `req/go_etcd_io_bbolt.md` yet at this writing; its `Api.lean` already
  uses `Model.lean` (`Data`, `bboltEntryMax`, `BoltSt.recovers` in its crash clause). To check at
  integration: the backend's `Snapshot` image (`boltImage`/`Tx.WriteTo.spec`), `Tx.Size`'s bound,
  `DeleteBucket`'s `ErrBucketNotFound` (`isErr`), `FillPercent` (`boltTx_fill`), the read
  transaction's `statSlot`, and `dbOpenOk` (4a's environment premise for `Open`'s error).

## `req/` sections written

`req/go_etcd_io_bbolt_internal_common.md` (new file, "from 4c"), `req/go_etcd_io_bbolt_internal_freelist.md`
(new file, "from 4c"), `req/go_etcd_io_bbolt_errors.md` ("from 4c (answer)").

## Round 1 repairs (review `reviews/4c-review-1.md`)

* **P1** (a commit after a failed sync): `BoltSt.commit`/`attempt` set `dur := none` once `lost`;
  filed `nonissues/bbolt-commit-after-failed-sync.md` (blocks-proof: no; etcd exits on a commit
  error).
* **P2**: 4c-D1 rewritten (the narrow physical rule, D22 covers the page cache only, the fake meta
  with a correct checksum; option (b) kept); 4c-D2 resolves the prophecy on "the page was written";
  `Tx.writeMeta.spec`'s `failed` covers an error reported after the page was written.
* **C1**: `Bucket.Put` takes `value ↦*{dv} vb` and lends it until the transaction is done
  (`putLoan`, `putLoan_done`); `ReqDefrag` in etcd's order (commit, then the source's rollback).
* **C2**: `Ent.wf` (inductive, transparent); laws `boltTx_wf` (views and committed data),
  `boltImage_wf`.
* **C3**: `boltLogger` transparent (D20′ restated with `logArgOk`), `openFileOk` transparent (over a
  provisional `osFileOf`, `req/os.md`), `writerPlain` from the method set; `Options.lean`: the
  literal, allocation, load, store, `optsAt` laws, per-field reads and stores (tracked and untracked).
* **C4**: `txSize tx n` (`boltTx_size`, `txSize_agree`); `Tx.Size` returns it, `Tx.WriteTo`'s image
  has that length.
* **C5**: `Tx.Rollback.spec` on a finished transaction (`ErrTxClosed`); `Begin`'s error is
  `dbClosed db ∨ dbBroken γ`, with `boltOpened_closed` and `dbBroken_state` (`BoltSt.broken`, set
  only by a commit that lost the mapping: the settling update's `brk`). `ReqDefrag` checks it.
* **C6**: `Commit` on a read transaction needs no update.
* **C7**: `ReqBackendBatch` checks `k2` is in the range and `k1` is not; Assumes the batch lock's
  `boltState`.
* **C8**: 94 internal specs (`node__*`, `Bucket__{node,openBucket,pageNode,write,free,dereference,
  inlineable,maxInlineBucketSize}`, `Cursor__{first_i,last_i,next_i,prev_i,seek_i,search,nsearch,
  keyValue,node,goToFirstElementOnTheStack}`, `DB__*` internals, `Tx__{allocate,close,rollback_i,page,
  forEachPage,check helpers}`, `TxStats__*`, `fdatasync`, `flock`, `mmap`, `munmap`, `newFreelist`,
  `splitThreshold`, `compareKeys`, `verifyKeyOrder`, `verifyPageReachable`, `Options__String`) over
  `Internal.lean`'s transparent model (`NodeR`, `TxCore`, `DbM`, `nodeSize`, `NodeR.put`/`del`,
  `splitIdx`) and opaque internal resources (`wtxCore`, `physRep`, `txPage`, `dbRaw`, `curPath`;
  `wtxCore_view`). A lowercase method whose name differs from a public one only in case gets the
  file suffix `_i` (`Tx__rollback_i`, `DB__close_i`, `Cursor__first_i`, ...), for case-insensitive
  file systems.
* **C9**: answered 4a (`req/go_etcd_io_bbolt.md`, "from 4c (answer)"): no file premise makes `Open`
  succeed (`dbOpenOk` stays an environment premise); the logger contract; the reader slot is the
  reading goroutine's `threadTok` under `Open`'s `2 ^ 29` bound (4a's `2 ^ 30 - 2` count not needed);
  `Size` = image length; `Close` gives `boltClosed`, not `fileHolds`.
* **Second tier**: S1 (`Update`'s `True` replaced by `fn`'s contract back on `Begin`'s error), S2/S3
  (every failed sync recorded by the settling update, which now fires on every error path), S5
  (snippets: concurrent readers of one read transaction, Assumes name the `boltState` holder,
  `γ.path` non-empty). Not done: S4 (the custom `OpenFile`'s file after `Open`'s error: `Open.spec`
  says nothing of it), S6 (the crash law's sketch), S7 (an abbreviation for `Commit`'s updates).
