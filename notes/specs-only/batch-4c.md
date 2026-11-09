# Batch 4c: bbolt's public API (DB, Tx, Bucket, Cursor)

Author's report, round 0 (2026-11-09). Namespace `Bbolt` (`Perennial.EtcdGrove.Bbolt`).
Build: `etc/specs-build.sh --dir Spec/go_etcd_io/bbolt`: OK, 54 modules.

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
* **Internal functions with old proved specs** (the old tree's `Proof/go_etcd_io/bbolt/` was
  complete: its collection rested only on the axiomatized `Options` type), not restated here:
  `Bucket.{node, openBucket, pageNode, write, free, dereference}`, `Cursor.{first, last, next,
  prev, seek, search, nsearch, keyValue, node, goToFirstElementOnTheStack}`, `DB.{freepages, grow,
  hasSyncedFreelist, meta, page, pageInBuffer, beginTx}`, `Tx.{allocate, close, forEachPage,
  page}`, `fdatasync`, `newFreelist`, `node.{childAt, childIndex, del, free, nextSibling,
  numChildren, prevSibling, put, read, removeChild, root, size, write}`, `TxStats.Inc*`,
  `Options.String`. Their specs are over the proof's internal vocabulary (the node cache's
  abstraction relation, the transaction registry, the file's shares), which the invariant design
  fixes; specs over a placeholder vocabulary now would be rewritten then. **Question 4c-Q5.**

## Decisions for the user (in plain terms first)

**4c-D1. What a crash leaves of a page being written (the sector rule).** bbolt keeps two copies
of its table of contents (the meta page), each 80 bytes at the start of a 4 KiB page, protected by
a checksum; a commit overwrites the older copy. OsFs's crash model (its D1) says every byte not yet
synced is *arbitrary* after a crash. Then a crash during a commit's meta write may leave the slot
holding garbage, and garbage can pass the 64-bit checksum (FNV-64a has collisions): bbolt would
then open a table of contents pointing anywhere and panic or return wrong data. No true axiom
excludes that (the bbolt-api example's D22 lesson). The physical fact bbolt relies on is that a disk
writes each 512-byte sector atomically (already one of OsFs's environment assumptions, "writes each
sector atomically", but not in its crash relation), so the 80 bytes come back either as they were
on disk or as some version the page cache held. Options: **(a)** refine OsFs's crash relation:
each aligned 512-byte sector of a crashed file holds its durable bytes or a version the page cache
held since the last sync (recommended: the physical fact, every client benefits; the bank test's
witness file already reasons this way); **(b)** keep the relation and give bbolt's closed theorems a
crash premise as minibolt's P1 (`CrashP1.lean`'s `osFsSemWith Q`), visible in every statement.
`boltCrash.spec` is true under (a) or (b), false under OsFs as it is.

**4c-D2. A prophecy on the meta write.** The commit update must fire when the meta write *starts*
(a crash during it may already find the new meta), but whether the commit takes effect is decided
when the write *ends* (it may fail with an errno and write nothing). The proof needs a prophecy of
the write's outcome: a prophecy patch `etc/proph-patches/bbolt/` adding `NewProph`/`ResolveBool(err
== nil)` around `writeMeta`'s `writeAt` (allowed by CLAUDE.md; recorded here as a proof need).
Alternative: two updates (an "attempt" at the start, the commit at the end): one more update every
`Commit` caller supplies.

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

**4c-Q5. The internal specs.** The old internal specs were proved (the old bbolt collection had no
`sorry`). PRINCIPLES: "a redesigned API keeps a spec for every function that already has a proved
spec"; its scope note: an internal helper "may simply mirror its code". Recommend: restate them
with the invariant design (this batch gives the commit path's five as the pattern); the user may
prefer them now over a placeholder internal vocabulary.

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
