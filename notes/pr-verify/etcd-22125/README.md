# pr etcd-io/etcd#22125: tests, probes and logs

Revisions: the PR head `a6c293d37` (etcd-io/etcd `pull/22125/head`); its upstream base `6006f4058`
(the merge base with `main`); the fork branch `pr-etcd-22125-goose-lean` of `mit-pdos/etcd-grove`
(`7931c5228`: the PR applied, cleanly, onto the fork's `goose-lean` `09669450f`). The Go tests run
with `GOTOOLCHAIN=go1.27.1`.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `maintenance_snapshot_test.go` | `TestSnapshotWriteToErrorReturns`: a `WriteTo` that writes 4 KiB of 96 KiB and fails with an I/O error makes `maintenanceServer.Snapshot` spin forever before the PR, return the error with it. `TestSnapshotWriteToEOFReturns`: the same failing with `io.EOF` spins forever before and after the PR. `TestBoltWriteToShortFileReturnsEOF`: bbolt v1.5.0's `Tx.WriteTo` returns `io.EOF` after 12288 of 233472 bytes when the database file is truncated under a read transaction (the `io.EOF` case is reachable from the real backend) | base, PR head, PR head + `guarded-loop.patch` | `cp maintenance_snapshot_test.go <etcd>/server/etcdserver/api/v3rpc/ && cd <etcd>/server && go test -run 'TestSnapshotWriteTo\|TestBoltWriteTo' -v ./etcdserver/api/v3rpc/` |
| `register_expiry_test.go` | `TestRegisterSessionExpiryNoGoroutineLeak`: 20 expiries of `grpcproxy.Register`'s session (its lease revoked, so the keepalive channel and `ss.Done()` close): the goroutine count stays at 39 and one lease is alive, before and after the PR: the goroutine leak the PR describes does not occur | base, PR head | `cp register_expiry_test.go <etcd>/tests/integration/proxy/grpcproxy/ && cd <etcd>/tests && go test -run TestRegisterSessionExpiryNoGoroutineLeak -v ./integration/proxy/grpcproxy/` |
| `guarded-loop.patch` | the suggested additional fix: the send loop fails on a read of no bytes; with it all three snapshot tests pass (and the package's tests) | PR head | `git apply guarded-loop.patch` in the checkout, then the first command |
| `logs/snapshot-base.log`, `logs/snapshot-pr.log`, `logs/snapshot-guarded.log` | the first command's output at the base, the PR head, and the PR head with the patch (zap's test-logger lines filtered out) | as named | as above |
| `logs/register-base.log`, `logs/register-pr.log` | the second command's output at the base and at the PR head | as named | as above |

The Lean side: `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/SnapshotLoop.lean` (the send
loop's termination model and its four theorems), restated with `#print axioms` in
`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/Results.lean`; build with
`lake build Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Results`.
