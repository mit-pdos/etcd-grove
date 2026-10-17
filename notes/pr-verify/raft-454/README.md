# Files for the etcd-io/raft#454 verification (`../raft-454.md`)

| File | What it shows | Runs against | Command |
|---|---|---|---|
| `pr454_test.go` | `TestPR454MixedBatchRejectedButAppended`: at a leader with a conf change pending, a `MsgProp` holding a normal entry and a conf change returns `ErrConfChangeRejected`, but the normal entry is appended, and so is an empty entry in place of the change. A later refused `RawNode.ProposeConfChange` also errors while the log grows (findings 1). `TestPR454NodeProposeConfChangeNoError`: `Node.ProposeConfChange` returns `nil` for a refused change (finding 2). Both pass, which shows the behavior. | the PR head `4e7ec16b82f369d37a258aadbcb35db2d7e24604` (etcd-io/raft, `git fetch raft-upstream pull/454/head`). Package `raft`, it uses internal test helpers. | `cp pr454_test.go <checkout at 4e7ec16b8>/ && GOTOOLCHAIN=go1.27.1 go test -run TestPR454 -count=1 -v .` |
| `pr454_test.out` | The output of that command at the PR head (2026-10-16): both tests pass. | same | (output) |
