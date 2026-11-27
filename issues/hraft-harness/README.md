# The hashicorp/raft issues' test harness

The `hraft-*` issues' tests (`issues/hraft-<slug>/*_test.go`) run hashicorp/raft's exported API over
two helpers of the verification fork's in-process test (dsverify-lab `examples/hraft/fork/raft` at
`02f88d5`), copied here unchanged but for their package paths: `inproc/` (an in-process
`raft.Transport` per server: every message a deep copy, the test's cuts and delays; heartbeats to the
handler raft sets, pipelined replication, InstallSnapshot), and `snapstore/` (an in-memory
`raft.SnapshotStore` with `FileSnapshotStore`'s semantics; `reader.go` is the fork's
`examples/snapstore/reader.go`). Neither is in upstream's tree, so the tests are a module of their
own, `hraftissue`, whose `github.com/hashicorp/raft` is replaced by the tree under test.

    issues/hraft-harness/run.sh RAFT [COUNT] [SLUG...]

runs each issue's test COUNT times (default 5) against the hashicorp/raft checkout RAFT (upstream
v1.8.0 `0f543c0`, upstream `main`, or the fork `examples/dsverify/hraft`), and prints the failures
and passes of each.
