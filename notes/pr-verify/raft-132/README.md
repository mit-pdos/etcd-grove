# Files for the verification of etcd-io/raft#132

The report is `../raft-132.md`. Each test runs against the PR head `e246b8d2f5d8eeae0bdbacfaf89a005cb0f2e705` (upstream etcd-io/raft, gogoproto `raftpb`; the PR's base is `d475d7e4a`). It does not run against the fork branch `pr-raft-132-goose-lean`, whose messages are protobuf-go v2 pointers.

| File | What it shows | Expected result at the PR head |
|---|---|---|
| `commit_track_pr132_test.go` | `TestProgressCommitAboveLeaderCommit`: 5 nodes. A follower learns commit index 2 from the old leader and reports it to a new leader whose commit is 0. This breaks the PR's documented invariants "Commit <= leader's commit index" and "sentCommit >= Commit". | FAIL, both invariants violated |
| `review_commit_lag_test.go` (written by the reviewer subagent) | `TestReviewLeaderOwnCommitLags`: the leader's own `Progress.Commit` lags its `committed`, because the self-ack carries the commit index from before `maybeCommit`. `TestReviewSnapshotCommitNotReported`: `handleSnapshot`'s `MsgAppResp` carries no `Commit`. | FAIL, both |
| `test-output-pr-head.txt` | Output of the three tests at the PR head (INFO/DEBUG log lines and message dumps filtered out). | as above |

To run them, from a checkout of etcd-io/raft at the PR head (`git fetch https://github.com/etcd-io/raft pull/132/head && git checkout FETCH_HEAD`):

    cp commit_track_pr132_test.go review_commit_lag_test.go <checkout>/
    cd <checkout> && GOTOOLCHAIN=go1.27.1 go test -run 'TestProgressCommitAboveLeaderCommit|TestReview' -v .

The fork's own test adaptation (`raft_paper_test.go`, `TestFollowerCheckMsgApp`) is committed on the fork branch `pr-raft-132-goose-lean` (`471242c60`), so it is not duplicated here.
