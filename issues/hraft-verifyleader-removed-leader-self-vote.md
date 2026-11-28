---
upstream: none
checked: 2026-11-27
links:
  - hashicorp/raft#725 issue open: related, not this bug: non-voters' responses counted (this one is the leader's own vote)
  - hashicorp/raft#740 pr open: #725's fix; it does not change the leader's own vote
blocks-proof: yes
---
# raft: `VerifyLeader` counts the leader's own vote after it removed or demoted itself, so its consistent read is stale

A leader that has appended its own `RemoveServer` or `DemoteVoter` (not yet committed) is not a voter
of its latest configuration, but `VerifyLeader` still counts its vote: with four voters and the leader
removing itself (quorum two of the three left), its own vote and one voter's heartbeat response
confirm it, while the two other voters have elected a newer leader that acknowledges writes. A
read served after `VerifyLeader` misses them.

**Expected:** `VerifyLeader` should succeed only when a quorum of the latest configuration's voters
confirms the leader, as the commitment and the lease count (Ongaro's dissertation, 4.2.2: a leader
not in the configuration does not count itself in majorities).

**Impact:** a user that reads its FSM after `VerifyLeader` (Consul's consistent reads) while the leader
removes or demotes itself (an operator's `RemoveServer` of the leader, or `DemoteVoter`); the window
lasts until the removing entry commits or the lease steps the leader down. Not fixed by #740.
Present in v1.8.0 and `main`.

**Reproduction:** `TestVerifyLeaderSelfVoteRemoved` and `TestVerifyLeaderSelfVoteDemoted` in
[`issues/hraft-verifyleader-removed-leader-self-vote/selfvote_test.go`](hraft-verifyleader-removed-leader-self-vote/selfvote_test.go),
run by [`issues/hraft-harness/run.sh`](hraft-harness/README.md) against hashicorp/raft@dd4346dbb127
(`main`, 2026-11-23) and v1.8.0 (`0f543c0`), go1.27.3 linux/amd64:

```
$ issues/hraft-harness/run.sh ../raft 5 hraft-verifyleader-removed-leader-self-vote
hraft-verifyleader-removed-leader-self-vote: 10 failed, 0 passed
    selfvote_test.go:355: stale read, not linearizable: W (Put "w") was acknowledged by S4, leader of term 3, before r began; r at L (S1), which had appended its own RemoveServer and so is not a voter of its latest configuration, passed every check of readAt way 2 (barrier of term 2 applied, VerifyLeader nil, term unchanged)
```

**Cause:** [`verifyLeader`](https://github.com/hashicorp/raft/blob/dd4346dbb127604c840301273c1441db09728bad/raft.go#L966-L975) starts every verify with `v.votes = 1` whatever the
leader's suffrage in its latest configuration; the leader steps down only once the entry removing it
commits.

## Proof

yes: the verification fork counts the leader's vote only if it is a voter of its latest
configuration (fork `4bb3955`, `examples/dsverify/hraft/raft.go`'s `verifyLeader`).
