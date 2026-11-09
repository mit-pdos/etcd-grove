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
