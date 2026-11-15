# Requirements on `go.etcd.io/etcd/server/v3/etcdserver/api/snap` (batch 2e)

## from 2f

Batch 2f (rafthttp) states these provisionally in `Rafthttp`'s `Api.lean` (section "Provisional");
replace them by snap's names at integration.

1. **`snapshotterOk ss`** (persistent): a `*Snapshotter` on which `SaveDBFrom` may run concurrently.
2. **`SaveDBFrom(r, id)`** with a reader `Http.readerAt r Pre Φ b` (the snapshot request's body after
   its envelope): reads `r` to `EOF` (its complete stream `bs`, with `Φ`), writes `bs` to a
   temporary file, syncs, renames it to the `.snap.db` of index `id` (or keeps an existing one);
   returns `(n, nil)` and **`dbSaved ss id bs`** (persistent: a database file of index `id` holding
   `bs` was in `ss`'s directory), or an error. Used by `snapshotHandler.ServeHTTP.spec` (`recvd`'s
   `dbSaved` for `Process`).
   ```go
   n, err := h.snapshotter.SaveDBFrom(r.Body, m.Snapshot.Metadata.GetIndex()) // http.go:275
   ```
3. **`snap.Message`** (`snapMsgOwn mp ml rc`, exclusive): `NewMessage(rs, rc, size)` gives it (the
   raft message `ml`, the reader wrapped in an `ExactReadCloser`, `TotalSize`) and keeps the receive
   side of `CloseNotify()` for the creator; `CloseWithError(err)` takes the close right (once:
   `closeC` has capacity 1) and closes the reader. The `ExactReadCloser` keeps the reader contract
   (`Http.readerAt`) of the reader it wraps, failing a stream of the wrong length. Used by
   `Transport.SendSnapshot.spec`, `createSnapBody.spec`, `snapshotSender.send.spec`.

## from 2d

1. **`snap.NewMessage(m, rc, size)`** (`createMergedSnapshotMessage`): the merged message (2d's
   `mergedSnap`), with `rc` a reader of the database image (`dbReader rc γ k`, provisional in
   `ApiApply.lean`) and `size` in `[0, 2^62)`; `CloseNotify()` a channel `sendMergedSnap`'s goroutine
   receives on once.
2. **The snapshotter's saved `.snap.db`** of a received merged snapshot (2f's `dbSaved`) is what
   `OpenSnapshotBackend` opens (`req/go_etcd_io_etcd_server_v3_storage.md`, from 2d, item 3).

### from 2f, round 1 (coordinating with 2e's `api/snap/Api.lean`)

Items 1-3 above are superseded. 2f now uses 2e's names: `Snap.isSnapshotter ss sd`, `Snap.snapDbs`,
`Snap.saveAt`, `Snap.dbReader`, `Snap.BeImage`, `Snap.isMessage`, `Snap.msgClose`. Two
requirements remain:

- **`SaveDBFrom.spec` as 2e states it** (an atomic update over `snapDbs sd F`, committing at
  `saveAt F id img`, with `dbReader r img`) serves 2f. The snapshot handler hands it the client's
  update (`Rafthttp.saveOk ν sd`). It turns the request body, read after the envelope, into
  `dbReader r.Body img` by `Rafthttp.readerAt_dbReader.spec`, over a pure stream relation
  `Rafthttp.imgBytes img bs` (provisional in 2f's Api: "`bs` is a stream of `img`"). Please adopt
  `imgBytes` (or name yours) and say in `dbReader`'s docstring that its bytes are such a stream.
  2f's `dbReader_readerAt.spec` (2e's `dbReader` gives `Http.readerAt rc True (imgBytes img)`) is
  the converse, for the sender's pipe.
- **The merged message's fields**: `Snap.isMessage p to sz` should also name the raft message
  pointer and the reader (`snap.Message.Message`, `ReadCloser`), which rafthttp reads
  (`createSnapBody`, `merged.Message`). 2f declares `snapMsgOwn mp ml rc` (persistent, read-only)
  provisionally.
