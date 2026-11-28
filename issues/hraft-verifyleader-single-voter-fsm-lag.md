---
upstream: none
checked: 2026-11-27
links:
  - hashicorp/raft#603 issue closed: related question (ReadIndex), not this bug
blocks-proof: yes
---
# raft: a read after `Barrier` and `VerifyLeader` (Consul's consistent read) can miss a write another server already returned

`VerifyLeader` answers once a quorum confirms the leader, without waiting for the leader's FSM to
apply the entries committed before it. With one voter (reachable with `DemoteVoter`/`RemoveServer`),
it answers at once. Another server can have applied a committed write and returned it to a read,
while a later read at the single voter, after a `Barrier` of its term and `VerifyLeader`, returns the
state before the write: a read that is not linearizable, with the recipe Consul's consistent reads
use (a barrier once per term, then `VerifyLeader`, then the FSM).

**Expected:** `VerifyLeader` should answer only once the FSM has applied every entry committed when it
was called (Raft's read-only queries, Ongaro's dissertation, 6.4, step 4), or its documentation should
say that the FSM may still lag the commit index after it returns.

**Impact:** a user that reads its FSM after `VerifyLeader` (Consul's `consistentRead`), in a cluster
where a server that is not the leader can apply entries before the leader does. The verification
fork's fix for three or more voters is `ea6e596` (every verified future through the FSM); the one-voter
path, which answers without the future, is `0c7aa12`. Upstream has neither.

**Reproduction:** `TestVerifyLeaderSingleVoterFSMLag` in
[`issues/hraft-verifyleader-single-voter-fsm-lag/single_voter_test.go`](hraft-verifyleader-single-voter-fsm-lag/single_voter_test.go),
run by [`issues/hraft-harness/run.sh`](hraft-harness/README.md) against hashicorp/raft@dd4346dbb127
(`main`, 2026-11-23) and v1.8.0 (`0f543c0`), go1.27.3 linux/amd64:

```
$ issues/hraft-harness/run.sh ../raft 5 hraft-verifyleader-single-voter-fsm-lag
hraft-verifyleader-single-voter-fsm-lag: 5 failed, 0 passed
    single_voter_test.go:379: not linearizable: r1 at j (S2) returned "w"; r2 at the leader K (S3, term 3, the only voter), begun after r1 returned, passed every check of readAt (barrier of term 3 applied, VerifyLeader nil, term unchanged) and returned {found:false value:} (K's FSM had not applied W
```

**Cause:** [`verifyLeader`](https://github.com/hashicorp/raft/blob/dd4346dbb127604c840301273c1441db09728bad/raft.go#L970-L975)'s hot path for a quorum of one responds at once, and
the quorum path responds from `leaderLoop` when the votes are counted: neither waits for `runFSM`.

## Proof

yes: the verification fork answers `VerifyLeader` through the FSM goroutine once every committed entry
is applied, on both paths (fork `ea6e596` and `0c7aa12`, `examples/dsverify/hraft/raft.go` and
`fsm.go`); `hraft_nocrash_robust`'s `VerifyLeader` reads need it.

## Notes

On upstream the test fails on the quorum path too (the fork's `ea6e596` is stage 2's fix of the same
lag, dsverify-lab `issues/verify-read-fsm-lag`); this test is the one-voter case the fork's stage 4
found after that fix.
