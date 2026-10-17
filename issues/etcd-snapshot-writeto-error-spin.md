---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#22125 pr open: propagates WriteTo's error with pw.CloseWithError; does not cover a WriteTo that ends early with io.EOF
---

# `maintenanceServer.Snapshot` spins forever when the snapshot ends early

**Status**: bug (a server goroutine that never returns and floods the client with empty
responses), reachable on a read error of the database file. That is the only route: etcd never sets bbolt's
`WriteFlag`, so `Tx.WriteTo` reads the already-open database file and fails only on a `pread`
error or a file shorter than `tx.Size()`; a defragmentation cannot close the file under it
(`db.Close` waits for the read transaction's mmap lock).

**Where**: `server/etcdserver/api/v3rpc/maintenance.go:152-156` (the writer goroutine:
`snap.WriteTo(pw)` with its error dropped, then `pw.Close()`) and lines 173-186 (the reader:
`for total-sent > 0`, `io.ReadFull` with `io.EOF` and `io.ErrUnexpectedEOF` tolerated), fork
`goose-lean` 09669450f.

**What happens**: if `snap.WriteTo` writes fewer than `snap.Size()` bytes (an I/O error), the pipe
ends with `EOF`; each further `io.ReadFull` returns `(0, io.EOF)`, which the loop accepts, so
`sent` stops below `total` and the loop sends an empty `SnapshotResponse` per iteration until the
client cancels the stream (`srv.Send` fails). `etcdctl snapshot save` without `--command-timeout`
never cancels. Reproduction: `notes/pr-verify/etcd-22066/maintenance_snapshot_test.go`,
`TestSnapshotWriteToError` (a snapshot that fails after 4096 bytes), on branch
`pr-verify/etcd-22066`: at the base the server sends responses until the test's stream refuses
the 1001st.

**Expected**: the stream ends with an error.

**How the proof handles it**: `Snapshot` is not verified. The loop's model
(`SnapshotLoopModel.lean`, `base_spins_on_writeTo_error`) proves the loop never ends when the
pipe yields fewer bytes than `snap.Size()`.

**Possible fixes**: `pw.CloseWithError(err)` on a `WriteTo` error (etcd#22125), and in the
reader, fail on a read of no bytes before `total` is reached (an `io.EOF` from `WriteTo` itself,
or any other short snapshot, still reaches the loop as a plain `EOF`).

**Found**: 2026-10-17, verifying etcd#22066 (`etcd-pr-verify`).
