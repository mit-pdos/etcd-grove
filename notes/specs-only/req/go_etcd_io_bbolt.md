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
