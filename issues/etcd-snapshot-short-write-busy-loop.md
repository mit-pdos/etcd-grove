---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#22125 pr open: fixes the case of a WriteTo error that is not EOF-like (CloseWithError); leaves a short WriteTo returning io.EOF looping (see "What happens")
---

# server: Maintenance/Snapshot busy-loops forever when the backend snapshot stops short

- **Status**: bug (a reachable non-terminating handler; liveness).
- **Where**: `server/etcdserver/api/v3rpc/maintenance.go` at the pinned revision (`etc/goose.py`,
  09669450f0ee): `maintenanceServer.Snapshot`, lines 150-157 (the writer goroutine:
  `snap.WriteTo(pw)`, its error dropped, then `pw.Close()`) and 173-200 (the send loop:
  `for total-sent > 0 { n, err := io.ReadFull(pr, buf); if err != nil && !errors.Is(err, io.EOF)
  && !errors.Is(err, io.ErrUnexpectedEOF) { return ... }; sent += n; srv.Send(...) }`, with
  `total = snap.Size()`). bbolt v1.5.0 `tx.go` `Tx.WriteTo` (copies `tx.Size()` bytes with
  `io.CopyN`, which returns `io.EOF` when the file holds fewer).
- **What happens**: when `snap.WriteTo` writes fewer than `snap.Size()` bytes (a read error of the
  database file, or a file shorter than the transaction's size), the pipe is closed normally, every
  later `io.ReadFull` returns `(0, io.EOF)`, which the loop ignores, `sent` stops growing and
  `total-sent > 0` stays true: the handler spins, calling `srv.Send` with an empty blob on every
  iteration (an endless stream of `SnapshotResponse{RemainingBytes: total-sent}`), for as long as the
  client keeps receiving: it ends only when the client cancels or disconnects (`srv.Send` fails).
  The client's `Snapshot` never sees an end or an error. (A file shorter than the transaction's size
  takes external truncation or corruption: defragmentation cannot cause it, since bbolt's `Close`
  waits for open read transactions.) Reproduction: `notes/pr-verify/etcd-22125/maintenance_snapshot_test.go`
  on branch `pr-verify/etcd-22125` (copy into `server/etcdserver/api/v3rpc/`, `go test -run
  'TestSnapshotWriteTo|TestBoltWriteTo' .`): `TestSnapshotWriteToErrorReturns` (WriteTo writes 4 KiB
  of 96 KiB and fails with an I/O error) and `TestSnapshotWriteToEOFReturns` (the same, failing with
  `io.EOF`) time out at the pinned code and at upstream main 6006f4058; `TestBoltWriteToShortFileReturnsEOF`
  shows bbolt's `Tx.WriteTo` returning `io.EOF` after 12288 of 233472 bytes when the file is
  truncated under a read transaction. The pure model's `snapshotLoop.old_hangs`
  (`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/SnapshotLoop.lean`) proves it for every
  short write.
- **Expected**: the RPC fails with the write's error (the client's `Snapshot` reports it), as for
  any other read error of the pipe.
- **How the proof handles it**: `Snapshot` is not verified (translated with its body on branch
  `pr-verify/etcd-22125` only); the loop's termination is a liveness property, outside what a
  Hoare triple states, and is the subject of the pure model above.
- **Possible fixes**: propagate the error (`pw.CloseWithError(err)`, pr etcd-io/etcd#22125; with
  `CloseWithError(nil)` equal to `Close()`, `_, err := snap.WriteTo(pw); snap.Close(); pw.CloseWithError(err)`
  keeps the old close order) and, for the `io.EOF` case that propagation cannot distinguish from
  the end of the stream, fail the loop on a read of no bytes (`if n == 0 { return error }`, or treat
  `io.EOF`/`io.ErrUnexpectedEOF` with `total-sent-n > 0` as an error): `snapshotLoop.guarded_terminates`.
- **Found**: 2026-10-17, verifying pr etcd-io/etcd#22125 (the pure model of the send loop and the
  Go tests above).
