# Requirements on `go.etcd.io/bbolt` (4c)

## from 4a

etcd's backend (`Spec/go_etcd_io/etcd/server/v3/storage/backend/`, namespace `Backend`) realizes its
vocabulary over bbolt's (`Spec/go_etcd_io/bbolt/Api.lean`): the file image `beFile p o` over
`fileHolds p D`, the history `beHist` over `boltState`'s committed data and `dur` (what a crash may
recover), the batch session over a write `boltTx`, the read side over a read `boltTx` shared by the
interval's readers. What the proof sketches need, by call site (`server/storage/backend/*.go`):

1. **`Open(path, 0600, opts)`** (`backend.go:225`, `newBackend`): from `fileHolds path D` (or no
   file: `fileHolds_new`), with the backend's options (`boltOpenOptions`: `MmapFlags =
   MAP_POPULATE`, `Mlock` off, `NoSync = UnsafeNoFsync`, `InitialMmapSize`, `Timeout`, the
   `*zapBoltLogger`), `isBolt db γ ∗ boltState γ 1 (BoltSt.init D)`; **an error only where an
   environment premise fails** (the file cannot be opened or locked, an mmap fails, the file is not
   a bbolt database): `newBackend` `lg.Panic`s on any error, so 4a's `New.spec` takes
   `Backend.dbOpenOk cfg` (opaque `Prop`, provisional): please name the premise under which `Open`
   succeeds (or state `Open`'s error cases so that 4a can define `dbOpenOk` from them). Used by
   `New.spec`, `newBackend.spec`.
2. **`*zapBoltLogger`'s contract** (`backend.go:1107-1120`): `newBoltLoggerZap` returns a pointer-typed
   `bolt.Logger` wrapping a zap `SugaredLogger` (`Warning`/`Warningf` added, the rest promoted);
   4a's `newBoltLoggerZap.spec` gives only its shape (`loggerPtrOk`); `Open` needs `boltLogger` of
   it: please state what the logger contract asks of a `*zapBoltLogger`-like value (a pointer type
   whose methods return), or accept a logger of a pointer type whose methods are zap's.
3. **`Begin(true)`/`Begin(false)`** (`backend.go:1067`, `unsafeBegin`; `Snapshot`, `:366`), the error
   `lg.Fatal` (no premise needed); a read transaction's reader slot: 4a lends one of its
   `beRdToks` (each counted against bbolt's `mmaplock` readers: `beReaderN ≤ 2^30 - 2`).
4. **`Tx.Commit()`** (`batch_tx.go:290`) on the batch write transaction: its update of `boltState`
   (`BoltSt.commit`, or `attempt` on an error, which `lg.Fatal`s): 4a fires its client's commit step
   (`commitOk`: the history gets the image) at that update. `Tx.Rollback()` of a read transaction
   (the rollback goroutine, `batch_tx.go:390`; `snapshot.Close`): `nil` for an open one.
5. **Buckets and cursors on the write transaction**: `Tx.Bucket(name)` (nil when absent),
   `CreateBucketIfNotExists` (an existing bucket unchanged), `DeleteBucket` (`ErrBucketNotFound`
   distinguishable: `errors.Is`), `Bucket.Put` (under `bboltEntryMax`; an empty or oversized key an
   error), `Bucket.Delete`, `Bucket.Cursor`/`Seek`/`Next` (in key order), `Bucket.ForEach`, and the
   `FillPercent` field written (`0.9`). The key and value slices a cursor returns are read-only for
   good in 4a's statements (`bytesListAt`, mvcc's contract): **say how long they stay readable in
   your model** (bbolt's documentation: until the transaction ends; mvcc's compaction uses them only
   within the session, its readers within the read transaction).
6. **On a read transaction**: `Tx.Bucket`, `Bucket.Cursor`/`Seek`/`Next`, `Bucket.ForEach` (the read
   side, `read_tx.go:62, 100-118`), concurrent with other readers of the same transaction under the
   backend's `txMu` (a cursor per reader; the bucket handles cached and shared).
7. **`Tx.Size()`, `Tx.WriteTo(w)`** (the snapshot, `backend.go:373`; promoted to `*snapshot`):
   `WriteTo` writes the bytes of a database file whose data is the transaction's (4a's `imgBytes I
   bs`, opaque, provisional: your `boltImage bs D` with `imgOf D = I`), `Size()` is their length, below
   `2^48` (4a's `imgBytes_size`); a write error stops after a prefix.
8. **`DB.Close()`** (`backend.go:483`): waits (`mmaplock`) for the open read transactions, gives
   `fileHolds path D` back for the committed data `D`, whatever its error. **`DB.Path()`, `Stats()`,
   `Info()`, `Tx.DB()`, `Tx.Stats()`**: any values (the size atomics, the metrics).
9. **The defragmentation** (trusted in 4a, names only): `OpenFile` custom (`openFileOk`), `Sync`, a
   rename of the copy over the file (OsFs), reopen: the same data; 4a states only that every image
   is unchanged.
10. **The flat image**: etcd uses only top-level buckets with plain values; 4a's `Image`
    (`made`, `ents`) is `imgOf D` (the root's buckets, their values; sequence counters dropped).
    A law `fileHolds_image`-style that a file reopened after `Close` holds the same `imgOf` is what
    4a's `beFile` round trip (`Close`, then `New`) rests on.

## from 4c (answer)

Item by item (`Spec/go_etcd_io/bbolt/`, namespace `Bbolt`; round 1 of 4c):

1. **When `Open` succeeds.** No file premise makes it succeed: in OsFs every system call `Open` makes
   (`open`, `flock`, `fstat`, `pread`, `pwrite`, `fdatasync`, `mmap`) may fail with an errno, so
   `Open.spec` has an error disjunct (`boltClosed γ` back). Keep `dbOpenOk` an environment premise
   of `New` (the closed-theorem convention for environment failures: an opaque premise, not a new
   adequacy theorem). An invalid file is excluded by the precondition (`boltFile γ`/`fileHolds`'s
   well-formedness), not an error. `Open` takes `boltFile γ ∗ boltClosed γ` (named once per
   generation by `fileHolds_alloc` from `fileHolds path D`; `fileHolds_new` for no file), and
   `boltState γ 1 (BoltSt.init D)` comes from `fileHolds_alloc`, not from `Open`: the state lives
   across opens.
2. **The logger contract** is now transparent (`Bbolt.boltLogger`, the old D20′ restated): nil, or a
   pointer-typed logger whose `Debugf`/`Errorf`/`Infof`/`Warningf` return for any format and any
   arguments meeting `logArgOk R` (a `fmt.ArgWf` basic value, an error whose `Error()` returns under
   `R`, a byte slice readable under `R`), reading only `args` and `R`. A `*zapBoltLogger` meets it
   from zap's `Sugar` printf methods: prove `boltLogger (newBoltLoggerZap's value)` in 4a.
3. **The read slot.** `Begin(false)` takes the caller's `threadTok` (D1: `isBolt`'s pool lends one
   `mmaplock` reader slot per thread token, under `Open`'s `ThreadBoundLe GF (2 ^ 29)`, D3), and
   `Rollback` gives it back. So 4a's readers each lend a thread's token rather than one of a counted
   stock: realize `beRdToks` as the reading goroutines' `threadTok`s (notes/bounds-plan.md: a bound
   is reasoned about where it is owned, here bbolt's pool); the `2 ^ 30 - 2` count is then not
   needed. `Begin(true)`'s error: `dbClosed db ∨ dbBroken γ`; the close right excludes the first
   (`boltOpened_closed`), and `dbBroken_state` the second for a client whose commits all succeeded
   (`σ.broken = false`): `lg.Fatal` on it is unreachable.
4. **Commit.** Two updates on `boltState γ 1 σ`: the commit update (`∀∀ ok`: `σ.commit T.cur ns` or
   `σ.attempt T.cur ns`) at the meta write, and the settling update (`σ.settle synced failed brk`) at
   the end; both fire on every write transaction's `Commit`, error or not. Fire your client's commit
   step at the first with `ok = true`. A read transaction's `Rollback`: `nil`; a finished one's:
   `ErrTxClosed` (`Tx.Rollback.spec`'s `none` case).
5. **Buckets and cursors.** As listed (`Tx.Bucket`, `Tx.CreateBucketIfNotExists` unchanged when the
   bucket exists, `Tx.DeleteBucket` with `isErr ErrBucketNotFound` and `errIs_distinct` for
   `errors.Is`, `Bucket.Put` under `bboltEntryMax` with `ErrKeyRequired`/`ErrKeyTooLarge`, `Delete`,
   `Cursor`/`Seek`/`Next` in key order by `boltTx_wf`, `ForEach`, `boltTx_fill`). **How long the
   returned slices stay readable**: while the transaction is live (`txBytes`, read through
   `txBytes_acc` with the transaction): not for good. A `Put`'s value is lent until the writer is
   done (`putLoan`, `putLoan_done`).
6. **The read side.** Fractions of the read transaction's `boltTx` for each reader (`boltTx_frac`),
   a cursor each (`Bucket.Cursor.spec` at any fraction), the handle shared (`bktH` persistent).
7. **`Size`/`WriteTo`.** `boltTx_size` gives `txSize tx n` with `n < 2 ^ 48`; `Tx.Size` returns `n`;
   `Tx.WriteTo` writes a prefix of an image `img` of `T.base` with `img.length = n`, all of it
   unless it fails (`boltImage img D`, opaque; your `imgBytes I bs` is `boltImage bs D` with
   `imgOf D = I`).
8. **Close.** `DB.Close.spec` gives `boltClosed γ` (with `dbClosed db`) to the close right's holder,
   whatever its error, not `fileHolds`: the file stays in `boltFile γ`'s crash invariant and the state
   `boltState γ 1 σ` with you; a reopen (`Open` with `boltClosed γ`) reads `σ.data`. This suits the
   `Close`-then-`New` round trip: no law on images is needed. `Path` (with the close right),
   `Stats` (`statSlot`), `Info` (a live transaction), `Tx.DB`, `Tx.Stats` (live or done): any values.
9. **Defrag.** `openFileOk f path` is transparent (an `*os.File` over a read-write fd of the path's
   OsFs file; `osFileOf` provisional, `req/os.md`); `Sync`'s update; `Options`' laws in
   `Spec/go_etcd_io/bbolt/Options.lean`. OsFs has no rename yet.
10. **The flat image.** Fine: `Data` is the root bucket; your `imgOf D` drops the sequences.
