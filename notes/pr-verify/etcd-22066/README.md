# pr etcd-io/etcd#22066: tests, patch and logs

Revisions: the PR head `ab1d5ade8` (etcd-io/etcd `pull/22066/head`); its upstream base `8d88b05e0`
(the merge base with `main`); the fork branch `pr-etcd-22066-goose-lean` of `mit-pdos/etcd-grove`
(`aa2031d07`: the PR applied onto the fork's `goose-lean` `09669450f`, one conflict resolved, see
the report). The Go tests run with `GOTOOLCHAIN=go1.27.1`.

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `maintenance_snapshot_test.go` | `TestSnapshotStream`: a snapshot of a 224 KiB database (8 responses) through `maintenanceServer.Snapshot` with a fake stream that refuses the 1001st `Send`. It checks that the stream ends, that the blobs add up to the size plus 32, and that each response's `RemainingBytes` is the bytes sent after it. It also logs `len(Blob)+RemainingBytes` per data response, which is what the PR's e2e test checks. `TestSnapshotWriteToError`: a snapshot whose `WriteTo` fails after 4096 bytes must end the stream with an error. | base, PR head, PR head + `suggested-fix.patch` | `cp maintenance_snapshot_test.go <etcd>/server/etcdserver/api/v3rpc/ && cd <etcd>/server && go test -count=1 -v -run 'TestSnapshot(Stream\|WriteToError)' ./etcdserver/api/v3rpc/` |
| `maintenance_snapshot_remaining_test.go` | `TestMaintenanceSnapshotStreamTerminates`: the same checks as `TestSnapshotStream` over a real one-member cluster's gRPC stream, with a 10 s deadline. | base, PR head, PR head + `suggested-fix.patch` | `cp maintenance_snapshot_remaining_test.go <etcd>/tests/integration/clientv3/ && cd <etcd>/tests && go test -count=1 -v -run TestMaintenanceSnapshotStreamTerminates ./integration/clientv3/` |
| `suggested-fix.patch` | The PR with the loop bound restored to `total-sent > 0`, keeping `RemainingBytes = totalByteToSend - sent`. | PR head | `git apply suggested-fix.patch` in the checkout, then either command |
| `logs/unit-base.log`, `logs/unit-pr.log`, `logs/unit-fix.log` | The first command's output (zap's test-logger lines filtered out). Base: the stream ends, but `RemainingBytes` is 32 short in every data response; `WriteToError` spins. PR head: `TestSnapshotStream` reaches the 1000-response cap, the last response being empty with `remaining_bytes:32`; `WriteToError` spins. With the fix: `TestSnapshotStream` passes, and the log shows `len(Blob)+RemainingBytes` equal to size+32 for the first response only; `WriteToError` still spins (the existing bug, `issues/etcd-snapshot-writeto-error-spin.md`). | as named | as above |
| `logs/integration-base.log`, `logs/integration-pr.log`, `logs/integration-fix.log` | The second command's output. Base: the count is 32 short (20480 vs 20512). PR head: 466,443 empty responses in 10 s, then `DeadlineExceeded`. With the fix: pass. | as named | as above |

The Lean side: `Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/SnapshotLoopModel.lean` (the
send loop's model and its theorems, with `#print axioms`); build with `lake build
Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.SnapshotLoopModel`.
