---
upstream: none
checked: 2026-11-08
links:
  - etcd-io/raft#381 pr open: related, a separate extended specification with the same vote condition (`votedFor[i] \in {Nil, j}`, no notion of a known leader)
blocks-proof: yes
---

# raft: TLA+ trace validation rejects a correct run in which a follower that knows its leader refuses a vote

A follower that has heard from its term's leader (an append request or heartbeat of that term)
without having voted refuses any vote request of that term, as raft intends: a term has one leader.
`tla/etcdraft.tla` has no notion of a known leader and grants such a request whenever the follower
has not voted, so trace validation (`tla/validate.sh` with `Traceetcdraft.tla`) rejects the trace of
a correct three-node run when the refusal reaches the candidate. Raft itself behaves correctly; the
specification does not describe its vote rule.

**Expected:** a trace of a correct run should pass `Traceetcdraft.tla`, as `tla/README.md`
describes: a failure "indicates a discrepancy between the model and its implementation".

**Impact:** trace validation of any application configured as `tla/README.md`'s example (no
PreVote, which the specification does not model) whose network delays a vote request past the
winner's first heartbeat. With three voters it takes a vote request delayed behind a later message
on the same link; with five voters, two candidates in one term suffice (a follower hears the winner's
heartbeat, then the loser's vote request), with every link in order. Such traces fail validation with
no bug in raft. raft v3.7.0 and `main` have the same specification and code.

**Reproduction:** `TestTLATraceVoteRefusedKnownLeader` in
[`issues/raft-tla-vote-refused-known-leader/tla_vote_known_leader_test.go`](raft-tla-vote-refused-known-leader/tla_vote_known_leader_test.go),
copied into the module root at etcd-io/raft@c51f010c851e (2026-10-23), go1.27.3 linux/arm64, with
`TLA_TOOLS` a directory holding the TLA+ tools `validate.sh` fetches (`tla2tools.jar` nightly 2.0
2026-11-06 and `CommunityModules-deps.jar` as downloaded 2026-11-08):

```
$ TLA_TOOLS=... go test -tags with_tla . -run '^TestTLATraceVoteRefusedKnownLeader$' -count=1 -v
    tla_vote_known_leader_test.go:170: Error: Temporal property TraceMatched was violated.
    tla_vote_known_leader_test.go:170: Error: The following behavior constitutes a counter-example:
    tla_vote_known_leader_test.go:172: Traceetcdraft rejects the trace of a correct raft run: exit status 12
--- FAIL: TestTLATraceVoteRefusedKnownLeader (1.18s)
```

The run: node 1 campaigns for term 2 and wins with node 2's vote; its vote request to node 3 is
delayed. Node 3 gets node 1's first heartbeat (term 2, leader 1, no vote), then the delayed vote
request, and refuses it. The trace is matched up to the line before node 1 receives the refusal
(line 54 of 54; with `MAX_TRACE=53` it passes): in the specification, node 3 granted the vote.

**Cause:** raft's vote rule ([`Step`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L1214-L1218))
grants only `r.Vote == m.From || (r.Vote == None && r.lead == None)`, and a follower sets `r.lead`
on an append request, heartbeat or snapshot of its term
([`stepFollower`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L1722-L1733)).
[`HandleRequestVoteRequest`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/etcdraft.tla#L508)
grants on `votedFor[i] \in {Nil, j}`, and the specification has no variable for the known leader.

## Proof

yes: the trace-check stage's statement (raft's traces conform to etcdraft.tla under upstream's trace validation) is false for runs that deliver a vote request to a voter that has not voted but already heard from the term's leader (notes/trace-validation-plan.md).

## Fix

No fix branch. [`fix.patch`](raft-tla-vote-refused-known-leader/fix.patch) (against `c51f010`) adds
raft's `lead` to `etcdraft.tla`: a per-server variable (in `serverVars`, initialized to `Nil` apart
from `InitServerVars`, which `MCetcdraft` and `Traceetcdraft` override) set to the sender by an
append request (`app`, `heartbeat`, `snapshot`) of the server's current term, whether accepted or
rejected for a log mismatch, and to itself by `BecomeLeader`; cleared by `BecomeFollowerOfTerm` (a
new term, or a step-down), `Timeout` and `Restart`, as `becomeFollower(term, None)`,
`becomeCandidate` and `newRaft` clear `r.lead`. The vote is granted on `votedFor[i] = j \/
(votedFor[i] = Nil /\ lead[i] = Nil)`. Every new value is a function of the state and the message,
so trace validation stays deterministic. One more change keeps it so: `NoConflictAppendEntriesRequest`
requires an entry of the request to be new. Without `lead`, its step on a request whose entries the
follower already holds changes nothing that `Traceetcdraft`'s `TraceView` sees (only `pl`), so TLC
merges it with the state it came from; with `lead`, it can set `lead` and becomes a second successor
beside `AppendEntriesAlreadyDone`'s, which `TraceMatched` rejects (found 2026-11-08 by random runs of
the corrected specification: a follower restarted, so with `lead` unset, receiving a delayed repeat of
an append request).

Checked 2026-11-08 at `c51f010` with the patch applied: the test passes, as does a five-voter
schedule (two candidates in term 2; node 5 hears leader 1's heartbeat, then refuses candidate 2),
which fails without it, and `tla/example.ndjson` still validates. `MCetcdraft` with
`MCetcdraft.cfg`'s bounds and invariants, less `LeaderCompletenessInv` and `MoreUpToDateCorrectInv`
(both false of the unpatched specification: etcd-io/raft#549, etcd-io/raft#515), found no violation
in 20 minutes of simulation (`-simulate -depth 80 -workers 4`: 126 million states, 1.5 million
behaviors) nor in 15 minutes of breadth-first search (to depth 15, 15 million distinct states).

## Notes

PreVote and `MsgForgetLeader` also touch `r.lead` (a pre-candidate clears it); the specification
models neither, so the patch leaves them out. Found 2026-11-08 by the trace-check stage's review of
Draft S4 (`notes/raft-trace-validation.md`, item 6); the schedules are `TestGap6ThreeVoters` and
`TestGap6FiveVoters` of `examples/raft/tracecheck/gaps_test.go`, rebuilt on upstream's `RawNode` and
`Traceetcdraft`.
