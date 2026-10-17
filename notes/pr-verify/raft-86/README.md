# Files behind `notes/pr-verify/raft-86.md`

All the Go files are tests of package `raft` (`go.etcd.io/raft/v3`). They run against
etcd-io/raft at the PR head `c976ceb6c` (branch `pr-raft-86` of the fork clone), or at its parent
`177ef28aa` (upstream `main` when the PR was opened) for comparison. To run one, copy it into a
checkout at that revision:

```
git -C ~/etcd worktree add --detach /tmp/raft86 c976ceb6c78d8aa3cf24647bc8455fa41ef675f2
cp notes/pr-verify/raft-86/<file>_test.go /tmp/raft86/
cd /tmp/raft86 && GOTOOLCHAIN=go1.27.1 GOFLAGS=-mod=mod go test -run '<Test>' -count=1 -v .
```

| File | What it shows | Revision | Test pattern |
|---|---|---|---|
| `raft_nextterm_test.go` | `TestNextTermWrapsInLastEpoch`: at `Term >= 2^64 - 2^16`, `becomeCandidate` moves the term **backwards**, to the 16-bit draw. `TestNextTermBounds`: below the last epoch the new term is the next epoch, later by less than `2^17` (what `nextTermOf_bounds` proves). `TestPreVoteTermDiffersFromElectionTerm`: the pre-vote's term and the election's are separate draws, and the election's is lower about half the time. All three pass; they only show the behavior. | PR head | `TestNextTerm\|TestPreVoteTermDiffers` |
| `raft_nextterm_test.log` | That run's output. | PR head | |
| `raft_review86_test.go` | The reviewer's tests. `TestReview86RaceDeposesNewLeader`: 3 nodes, PreVote and CheckQuorum on, two concurrent candidates. The one that loses has a higher random term, deposes the new leader with a `MsgAppResp` at its term, and cannot win itself. This happens in about 100 of 200 runs at the PR head and 0 at the parent. `TestReview86PreVoteGrantedVoteIgnored`: a peer at term `P` grants a pre-vote at `T1 > P` and then ignores the election's `MsgVote` at `T2 <= P`. This happens in about half of the granted pre-votes at the PR head, and never at the parent. Both tests fail at the PR head and pass at the parent. | PR head and parent | `TestReview86` |
| `raft_review86_test.pr-head.log`, `raft_review86_test.base.log` | Their output at the PR head and at the parent. | | |
| `pr-head-failing-tests.log` | The 38 existing tests of package `raft` that fail at the PR head. They hard-code terms `r.Term + 1`; the PR changes none of them. All pass at the parent. | PR head | `go test .` |
