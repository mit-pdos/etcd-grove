---
upstream: known
checked: 2026-11-08
links:
  - etcd-io/raft#515 issue open: this bug, found from the specification alone (a five-server counterexample through a heartbeat-free path: a commit index carried by an append request with one entry); no comments or PR
  - etcd-io/raft#549 issue open: related, not this bug: another of etcdraft.tla's invariants (LeaderCompletenessInv) false
blocks-proof: yes
---

# raft: TLA+ trace validation rejects a correct run with small `MaxSizePerMsg` (`MoreUpToDateCorrectInv` is false)

`tla/etcdraft.tla`'s `MoreUpToDateCorrectInv` requires a server whose log is at least as up to date
as another server's to hold that server's committed entries. A follower can learn its commit index
from a heartbeat while its log ends at an old-term entry that a server with a newer-term last entry
lacks, so trace validation (`tla/validate.sh` with `Traceetcdraft.tla`) rejects the trace of a
correct five-node run whose append requests carry one entry each, reporting `Invariant
MoreUpToDateCorrectInv is violated`. The specification itself reaches the same violation.

**Expected:** a trace of a correct run should pass `Traceetcdraft.tla`, as `tla/README.md`
describes ("a discrepancy between the model and its implementation"); and the specification's
invariants should hold of the specification.

**Impact:** trace validation of applications whose append requests do not carry the leader's log to
its end (a `MaxSizePerMsg` smaller than a batch of entries, or the inflight limit) can fail with no
bug in raft. Model checking the specification long enough finds it too, outside `MCetcdraft.cfg`'s
limits on duplicate append requests (`MCSend`). raft v3.7.0 and `main` have the same specification.

**Reproduction:** `TestTLATraceMoreUpToDateCutBatches` (raft's trace) and
`TestTLAModelMoreUpToDateCutBatches` (the specification alone) in
[`issues/raft-tla-more-up-to-date-cut-batches/tla_more_up_to_date_test.go`](raft-tla-more-up-to-date-cut-batches/tla_more_up_to_date_test.go),
copied into the module root at etcd-io/raft@c51f010c851e (2026-10-23), go1.27.3 linux/arm64, with
`TLA_TOOLS` a directory holding what `validate.sh` downloads (`tla2tools.jar`, nightly 2.0
2026-11-06, and `CommunityModules-deps.jar`, as of 2026-11-08):

```
$ TLA_TOOLS=... go test -tags with_tla . -run '^TestTLA(Trace|Model)MoreUpToDateCutBatches$' -count=1 -v
=== RUN   TestTLATraceMoreUpToDateCutBatches
    tla_more_up_to_date_test.go:59: Error: Invariant MoreUpToDateCorrectInv is violated.
    ...
    tla_more_up_to_date_test.go:61: Traceetcdraft rejects the trace of a correct raft run: exit status 12
--- FAIL: TestTLATraceMoreUpToDateCutBatches (2.88s)
=== RUN   TestTLAModelMoreUpToDateCutBatches
    tla_more_up_to_date_test.go:447: replay: Error: Invariant MoreUpToDateCorrectInv is violated.
    ...
    tla_more_up_to_date_test.go:463: replay: not within MCetcdraft.cfg's limits (MCTimeout, MCSend, MCClientRequest): stops at state 235 of 243
    tla_more_up_to_date_test.go:76: etcdraft.tla itself (from MCetcdraft's Init, 242 steps of NextAsync or stutter) reaches a state violating MoreUpToDateCorrectInv
--- FAIL: TestTLAModelMoreUpToDateCutBatches (10.00s)
```

The run (five voters, `MaxSizePerMsg` 1): node 1 is elected for term 2 and its entry x at index 6
reaches node 3 only; node 2 is elected for term 3 and its entry y at index 6 reaches node 4 only;
node 1 is elected for term 4 (nodes 2 and 4 refuse and follow term 4, so no leader is stale),
appends z at 7, replicates z to nodes 3 and 4 (committing 7, and with it x) and x alone to node 5;
a heartbeat gives node 5 the commit index `min(match 6, 7) = 6`. Node 5's log ends at x (term 2),
committed; node 2's ends at y (term 3), at least as up to date, and lacks x.

The second test replays the states of TLC's counterexample, the specification's variables only,
against `MCetcdraft.tla` from its `Init`, each step an action of `NextAsync` (a disjunct of `Next`)
or a stutter landing exactly on the next recorded state, with deadlock checking on: TLC reproduces
all 243 states and reports the invariant violated at the last. With `MCetcdraft.cfg`'s limits on,
the replay stops at state 235 (`MCSend` allows one append request per pair and term in flight).

**Cause:** [`MoreUpToDateCorrectInv`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/etcdraft.tla#L848-L852)
compares the two logs' last entries, but a commit index learned from a heartbeat (a heartbeat
[carries](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/etcdraft.tla#L339) `Min({commitIndex[i], matchIndex[i][j]})`) can cover an entry the follower got from a leader
without that leader's own last term, so the follower's last entry need not be of the committing
term. Raft's argument (a log more up to date than a quorum member holding the committing leader's
entry contains the committed entries) needs the committing term, which the specification does not
record.

## Proof

yes: the trace-check stage's statement (raft's traces conform to etcdraft.tla under upstream's trace validation) is false for runs where a follower learns a commit index past the leader's entries it holds (notes/trace-validation-plan.md).

## Fix

No patch. The invariant needs the term in which each entry was committed (a history variable set
when a leader's `commitIndex` first covers it), and then reads: a server whose log is at least as up
to date as a log holding an entry of the committing term, at or after the committed index, holds the
committed entries. Dropping the invariant is the alternative.

## Notes

Found 2026-11-08 by the trace-check stage's review (S4 round 3), `TestGap8MoreUpToDate` in
`examples/raft/tracecheck/gaps_test.go`. Evaluating `Next` in state 212 of this replay fails
(`raft-tla-restart-truncated-log`), which is why the replay uses `NextAsync`: no recorded step is a
crash or a network fault.
