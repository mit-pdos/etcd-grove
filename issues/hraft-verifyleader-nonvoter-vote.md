---
upstream: known
checked: 2026-11-27
links:
  - hashicorp/raft#725 issue open: this bug
  - hashicorp/raft#740 pr open: the fix (verifyLeader registers the future with voters' replications only)
blocks-proof: yes
---
# raft: `VerifyLeader` counts a non-voter's heartbeat response as a vote, so a deposed leader's consistent read is stale

A leader cut off from the other voters but still reaching a non-voter gets a successful
`VerifyLeader`: the non-voter's heartbeat response is counted toward the voters' quorum. Meanwhile
the voters have elected a new leader, which commits and acknowledges writes, and a read the deposed
leader serves after `VerifyLeader` misses them.

**Reproduction:** `TestVerifyLeaderNonvoterVote` in
[`issues/hraft-verifyleader-nonvoter-vote/nonvoter_vote_test.go`](hraft-verifyleader-nonvoter-vote/nonvoter_vote_test.go)
(three voters and a non-voter over an in-process transport; a leadership transfer moves the
leadership while the old leader still reaches the non-voter), run by
[`issues/hraft-harness/run.sh`](hraft-harness/README.md) against hashicorp/raft@dd4346dbb127 (`main`,
2026-11-23) and v1.8.0 (`0f543c0`), go1.27.3 linux/amd64:

```
$ issues/hraft-harness/run.sh ../raft 5 hraft-verifyleader-nonvoter-vote
hraft-verifyleader-nonvoter-vote: 5 failed, 0 passed
    nonvoter_vote_test.go:350: not linearizable (stale read): W (Put "w") was acknowledged by the leader j (S2, term 3, voters j and S3); r1 at K (S1), begun after that, passed every check of readAt (barrier of term 2 applied, VerifyLeader nil, term unchanged) and returned {found:false value:}
```

**Cause:** [`verifyLeader`](https://github.com/hashicorp/raft/blob/dd4346dbb127604c840301273c1441db09728bad/raft.go#L966-L988) registers the future with every replication
goroutine, non-voters' included, and `verifyFuture.vote` counts every successful heartbeat response
toward `quorumSize`, a majority of the voters.

## Proof

yes: the verification fork counts only the latest configuration's voters' responses (fork
`6c3454c`, `examples/dsverify/hraft/raft.go`'s `verifyLeader`); `hraft_nocrash_robust`'s reads
through `VerifyLeader` need it.
