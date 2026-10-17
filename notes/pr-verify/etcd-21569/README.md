# Files for the etcd-io/etcd#21569 verification

Report: `notes/pr-verify/etcd-21569.md`. Revisions:

- **base**: the fork's `goose-lean` pin `09669450f` (upstream `main` plus the Goose rewrites; it
  contains the PR's merge-base `e48b0e662`).
- **fork PR**: `mit-pdos/etcd-grove` branch `pr-etcd-21569-goose-lean`, commit `cf6715b45`: the base
  plus the PR's non-test diff, with `proto.Size(rs)` kept (the PR head's `rs.Size()` does not
  compile).
- **PR head**: upstream `8d183a2e9`. It does not build (`pr-head-build.log`), so no test runs there.
  The fork PR is the PR's behavior.

Go tests are run from the module's directory with `GOTOOLCHAIN=go1.27.1`, after copying the file
into the package.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `snapshot_truncated_test.go` (package `rafthttp`) | A snapshot whose database stream ends early with a clean `io.EOF` (what `newSnapshotReaderCloser` produces when bbolt's `Tx.WriteTo` returns `io.EOF`) is reported as sent. The receiver keeps the truncated `.snap.db`. Passes at the base, fails at the fork PR. | base, fork PR | `cp snapshot_truncated_test.go <checkout>/server/etcdserver/api/rafthttp/ && cd <checkout>/server && go test ./etcdserver/api/rafthttp/ -run TestSnapshotSendTruncatedByEOF -v` |
| `snapshot_long_test.go` (package `rafthttp`) | The existing `TestSnapshotSend` case #3 on its own: 5 bytes for a declared 1 are sent and kept with the PR. `TestSnapshotSend` stops at case #2 (`t.Fatalf`). A regression in the test only: in production `Tx.WriteTo` never writes more than `tx.Size()`. | base, fork PR | same, `-run TestSnapshotSendLongerThanDeclared` |
| `rafthttp-base.log`, `rafthttp-pr.log` | Output of `-run TestSnapshotSend` (the existing test, the two above) at the base (all pass) and at the fork PR. At the fork PR, the existing `TestSnapshotSend` fails at case #2 ("snapshot expected false, got true"; "expected 0 files, got 1 files"). | base, fork PR | `go test ./etcdserver/api/rafthttp/ -run TestSnapshotSend -count=1 -v` |
| `pr-head-build.log` | `go build` of `server/etcdserver/api/snap` at the PR head: `rs.Size undefined (type *raftpb.Message has no field or method Size)`. | PR head | `cd <checkout>/server && go build ./etcdserver/api/snap/` |
| `readcloser_eof_test.go` (package `ioutil`) | `issues/etcd-exactreadcloser-eof-with-data.md`: an exact reader over a reader that returns its last bytes with `io.EOF` reads 5 of 10 bytes with no error. Fails at the base (latent: no etcd caller's reader does this). | base | `cp readcloser_eof_test.go <checkout>/pkg/ioutil/ && cd <checkout>/pkg && go test ./ioutil/ -run TestExactReadCloserShortWithDataEOF -v` |
| `astdiff/` (`main.go`, `go.mod`), `astdiff.log` | Step 3: the functions whose `go/ast` differs between the base and the fork PR in the PR's two files: `NewMessage` and `newSnapshotReaderCloser`. | base vs fork PR | `cd astdiff && go run . <base checkout> <fork PR checkout> server/etcdserver/api/snap/message.go server/etcdserver/snapshot_merge.go` |
| `bolttrunc/` (`trunc_test.go`, `go.mod`, `go.sum`; the reviewer's), `bolttrunc.log` | What the follower does with such a file. The test builds a ~41 MB bbolt db, keeps a quarter of its `Tx.WriteTo` output (the meta pages intact), and opens that with etcd's backend options (10 GiB `InitialMmapSize`, map freelist) in a child process. `bolt.Open` dies with SIGBUS in `loadFreelist`. The test passes and prints the child's crash. | bbolt v1.5.0 (etcd's pin) | `cd bolttrunc && GOFLAGS=-mod=mod go test -v -count=1 .` |
