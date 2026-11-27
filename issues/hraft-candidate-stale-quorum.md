---
upstream: none
checked: 2026-11-27
links:
  - hashicorp/raft#727 issue open: related, not this bug: a leadership transfer to a non-voter
blocks-proof: yes
---
# raft: a candidate counts its votes against the quorum of the configuration it had before its pre-vote, and two leaders win one term

`runCandidate` fixes the number of votes it needs before the pre-vote, but asks for votes from the
configuration latest when the election starts. A candidate that received `TimeoutNow` during its
pre-vote accepts AppendEntries of its own term without stepping down, and can store a configuration
entry meanwhile (`AddVoter`: five voters become six). It then wins with three votes of six, while the
three other servers of the five-voter configuration elect one of them in the same term.

**Expected:** a candidate should win only with a majority of the voters it asked, the latest
configuration's (Raft, §4.1; election safety, §5.2: at most one leader per term).

**Impact:** a cluster whose leader is asked for a leadership transfer that times out (the target
in its pre-vote: its vote requests held up) and then for a membership change, both of which an
operator can ask through the API; a split brain in one term, each leader committing its own entries.
Rare: the schedule needs the transfer's timeout and the change to meet in one candidate's pre-vote.
Present in v1.8.0 and `main`.

**Reproduction:** `TestCandidateStaleQuorum` in
[`issues/hraft-candidate-stale-quorum/stalequorum_test.go`](hraft-candidate-stale-quorum/stalequorum_test.go)
(six servers over an in-process transport; a leadership transfer that times out at the leader, then
`AddVoter`), run by [`issues/hraft-harness/run.sh`](hraft-harness/README.md) against
hashicorp/raft@dd4346dbb127 (`main`, 2026-11-23) and v1.8.0 (`0f543c0`), go1.27.3 linux/amd64:

```
$ issues/hraft-harness/run.sh ../raft 5 hraft-candidate-stale-quorum
hraft-candidate-stale-quorum: 5 failed, 0 passed
    stalequorum_test.go:518: election safety violated: servers [2 3] were each leader of term 3. S2 won with three votes (its own, S1's and S6's), counted against the quorum of O = {S1..S5} (three) computed before its pre-vote, though it asked the voters of N = {S1..S6} (quorum four)
```

**Cause:** [`runCandidate`](https://github.com/hashicorp/raft/blob/dd4346dbb127604c840301273c1441db09728bad/raft.go#L317)'s `votesNeeded := r.quorumSize()` is computed once, before
the pre-vote; [`electSelf`](https://github.com/hashicorp/raft/blob/dd4346dbb127604c840301273c1441db09728bad/raft.go#L1999) asks the voters of the configuration latest after it, and
[`appendEntries`](https://github.com/hashicorp/raft/blob/dd4346dbb127604c840301273c1441db09728bad/raft.go#L1480) does not make a candidate from a leadership transfer step down for
an AppendEntries of its own term.

## Proof

yes: the verification fork recomputes `votesNeeded` from the latest configuration after the pre-vote
(fork `02f88d5`, `examples/dsverify/hraft/raft.go`'s `runCandidate`).
