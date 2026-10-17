---
upstream: none
checked: 2026-10-17 (gh search of etcd-io/etcd issues and PRs for "ExactReadCloser": only #21569)
links:
  - etcd-io/etcd#21569 pr open: removes NewExactReadCloser's only use (snap.NewMessage); does not touch this
---

# `ioutil.ExactReadCloser` passes a short stream's `io.EOF` through when it comes with data

**Status**: a gap between the code and its documentation, latent in etcd: no caller's reader
triggers it.

**Where**: `pkg/ioutil/readcloser.go:34-54` (fork `goose-lean` `09669450f`, upstream `main`
the same): `NewExactReadCloser` "returns a ReadCloser that returns errors if the underlying reader
does not read back exactly the requested number of bytes". `Read` checks for a short stream only on
an empty read (`e.br < e.totalBytes && n == 0`).

**What happens**: `io.Reader` allows a reader to return its last bytes together with `io.EOF`
(`n > 0, err == io.EOF`). When that last read leaves the stream short of `totalBytes`, `Read`
returns `(n, io.EOF)` unchanged: `io.ReadAll`, `io.Copy` and `io.MultiReader` see a clean end of a
truncated stream. Only `Close` then returns `ErrShortRead`. Reproduction:
`notes/pr-verify/etcd-21569/readcloser_eof_test.go` (package `ioutil`), which fails at
`09669450f` with `read 5 of 10 bytes with no error ("hello")`.

In etcd the one caller, `snap.NewMessage`, wraps the `io.PipeReader` of
`etcdserver.newSnapshotReaderCloser`, and a pipe never returns data together with `io.EOF`. So
the snapshot sender is not affected. It would be if the wrapped reader were ever one that does
this (`testing/iotest.DataErrReader` makes any reader do it). In the sender (`rafthttp/snapshot_sender.go`), a `Close`-time `ErrShortRead` only reaches
`merged.CloseWithError`, which runs after `ReportSnapshot(SnapshotFinish)` and makes `CloseNotify`
report `false`. Raft is not told, and the receiver has already saved the stream.

**Expected**: `Read` returns `ErrShortRead` whenever the stream ends (`err == io.EOF`) before
`totalBytes`, whatever `n` is.

**How the proof handles it**: `Spec/go_etcd_io/etcd/pkg/v3/ioutil/exactReadCloser__Read.lean`
states what the code does, `exactReadResult` (`Proof/go_etcd_io/etcd/pkg/v3/ioutil/Defs.lean`). Its
guarantee, `exact_end`, holds only for a result passed through from an empty underlying read
(`n = 0`), which is how a pipe reports its end. Branch `pr-verify/etcd-21569`.

**Possible fixes**: in `Read`, after counting, `if err == io.EOF && e.br < e.totalBytes { return n,
ErrShortRead }` (or return the bytes with `nil` and report `ErrShortRead` on the next call).

**Found**: 2026-10-17, verifying etcd PR #21569 (the spec of `exactReadCloser.Read`).
