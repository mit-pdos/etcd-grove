---
upstream: known
checked: 2026-11-28
links:
  - hashicorp/raft#746 issue open: this bug (found with Antithesis, pre-vote off)
  - hashicorp/raft#747 pr open: a fix, the candidate written before the term
  - hashicorp/raft#661 issue closed: related, not this bug: the same two writes, claimed to allow a double vote (a false positive)
blocks-proof: yes
---
# raft: a crash between the two writes of a vote lets the server vote, after its restart, for a candidate whose log is behind its own

`persistVote` stores a vote as two separate stable-store writes, the term (`LastVoteTerm`), then
the candidate (`LastVoteCand`). A server that crashes between them restarts holding the new term
with the candidate of an older vote. When that older candidate asks for its vote in the new term,
`requestVote` takes the pair for a vote it already gave and grants it again, without comparing the
candidate's log with its own. A candidate missing committed entries can then be elected, and it
overwrites them.

**Expected:** a server should grant a vote only to a candidate whose log is at least as up to date
as its own (Raft, §5.4.1), after a crash as before it; the stable store's writes are each durable
when they return (`StableStore`'s contract), but two of them are not one atomic step.

**Impact:** any deployment whose stable store makes each `Set` durable on its own (raft-boltdb: one
transaction per call), with or without pre-vote, when a server crashes while voting in an election
that one of its earlier vote's candidates later runs in. Present in v1.8.0 and `main`.

**Reproduction:** two tests in
[`issues/hraft-persistvote-torn-vote/vote_test.go`](hraft-persistvote-torn-vote/vote_test.go), one real
server, B, and two peers, A and X, played by the test: `TestTornVoteGrantsWithoutLogCheck` takes B's
stores as a crash leaves them before and after each of its stable-store writes during its vote for A,
and restarts B from each; `TestTornVoteFailedWrite` fails, once, whichever of the vote's two writes comes
second (an I/O error, no restart). Run by [`issues/hraft-harness/run.sh`](hraft-harness/README.md)
against hashicorp/raft@dd4346dbb127 (`main`, 2026-11-23) and v1.8.0 (`0f543c0`), go1.26.0 linux/amd64:

```
$ issues/hraft-harness/run.sh ../raft 5 hraft-persistvote-torn-vote
hraft-persistvote-torn-vote: 10 failed, 0 passed
    vote_test.go:311: B, crashed before writing LastVoteCand of its vote for A in term 4 (stable store:
      CurrentTerm 4, LastVoteTerm 4, LastVoteCand "X" ...) and restarted, granted X's vote in term 4 though
      X's last entry (1, 1) is older than B's (2, 3): X leads term 4 with B's vote and its own without the
      committed entry 2
    vote_test.go:317: state-machine safety violated: B applied "e" at index 2, then "f" after the restart
    vote_test.go:361: B, whose vote for A in term 4 failed between its two writes (stable store: CurrentTerm 4,
      LastVoteTerm 4, LastVoteCand "X" ...), granted X's vote in term 4 though X's last entry (1, 1) is older
      than B's (2, 3)
```

**Cause:** [`persistVote`](https://github.com/hashicorp/raft/blob/dd4346dbb127604c840301273c1441db09728bad/raft.go#L2153-L2161) writes `LastVoteTerm` and `LastVoteCand`
separately; [`requestVote`](https://github.com/hashicorp/raft/blob/dd4346dbb127604c840301273c1441db09728bad/raft.go#L1721-L1727) grants without the log check when both match
the request ("duplicate requestVote"), a shortcut sound only if the two were written together.
`electSelf`'s vote for itself has the same window.

## Proof

yes: the proof's vote coupling cannot be established with upstream's order (R1, #48 7237493407).
The verification fork writes the candidate before the term, as upstream's PR #747 does, in
hashicorp's storage format (`examples/dsverify/hraft/raft.go`'s `persistVote`; branch
`hraft-r0-fixes/2026-11-28`, pending): a torn write then leaves the older vote's term with the new
candidate, below the current term the server persisted first, which `requestVote` never takes for a
vote of the current term. Both tests pass on the fork (5 of 5 each).
