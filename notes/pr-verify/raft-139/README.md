# Files for `notes/pr-verify/raft-139.md`

Each Go file is a test file of package `raft` (the root package of etcd-io/raft). To run it,
copy it into the root of a checkout of the revision named and run the command there
(`GOTOOLCHAIN=go1.27.1`).

| File | What it shows | Revisions | Command |
|---|---|---|---|
| `leaderterm_probe_test.go` | Three behaviour changes of the PR. `TestProbeLeaderEmptyEntryDropped`: with a storage whose last entry's term (3) is above the persisted term (no `HardState`), the new leader's empty entry is silently not appended (`raftLog.append(1, ...)` returns early). `TestProbeMsgAppEntryAboveMsgTerm`: a `MsgApp` of term 2 carrying an entry of term 3 now panics (`leader at term 2 tries to append a higher term 3`). `TestProbeSnapshotFastForwardSkipped`: a snapshot whose last entry the follower already has, from a leader of a term the log's `leaderTerm` is not at, no longer fast-forwards the commit index. | PR head `4e08f525c` (all three fail), base `026484c68` (all pass) | `go test -count=1 -run TestProbe -v .` |
| `review_snapstall_test.go` (written by the reviewer subagent) | `TestReviewSnapFastForwardStall`: the skipped fast-forward leaves the leader's progress for that follower in `StateSnapshot` (its reply carries the old commit index), so without the application's `ReportSnapshot` the follower gets nothing more and its commit index stays put; at the base it reaches `StateReplicate` and commits up to 8. `TestReviewNoConflictAppendNoCommit`: an accepted `MsgApp` with no new entries, from a leader of a newer term than the log's `leaderTerm`, commits nothing (base: commits 2). | PR head `4e08f525c` (both fail), base `026484c68` (both pass) | `go test -count=1 -run TestReview -v .` |
| `probes-pr.log`, `probes-base.log` | The output of both files at the PR head and at the base (`go test -count=1 -run 'TestProbe\|TestReview' -v .`, raft's own log lines removed). | as named | |

The PR applied to the verified base (raft v3.7.0 plus the read-index fix) is commit `1daf55cb3` of
branch `pr-raft-139-goose-lean` of the Goose fork (`~/etcd`); its own tests (`go test ./...`) pass
there.
