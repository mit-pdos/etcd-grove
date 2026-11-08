---
upstream: known
checked: 2026-11-08
links:
  - etcd-io/raft#549 issue open: this bug, found from the specification alone (a TLC counterexample of etcdraft.tla); proposes a repaired invariant, no comments or PR yet
blocks-proof: yes
---

# raft: TLA+ trace validation rejects a correct run with a stale leader (`LeaderCompletenessInv` is false)

`tla/etcdraft.tla`'s `LeaderCompletenessInv` requires every current leader whose term exceeds a
committed entry's term to hold that entry. A leader that has not yet learned of a newer term (with
`CheckQuorum` off, as in `tla/README.md`'s example configuration) need not hold an entry committed in
a later term, so trace validation (`tla/validate.sh` with `Traceetcdraft.tla`) rejects the trace of
a correct three-node run, reporting `Invariant LeaderCompletenessInv is violated`.

**Expected:** a trace of a correct run should pass `Traceetcdraft.tla`, as `tla/README.md`
describes: a failure "indicates a discrepancy between the model and its implementation". Raft's
leader completeness property (the Raft paper, §5.4) is about leaders of terms after the term in
which an entry was committed, not after the entry's own term.

**Impact:** trace validation of any application whose cluster can have a stale leader (any
partition or message loss lasting an election) can fail with no bug in raft. etcd runs with
`CheckQuorum`, which narrows the window (a stale leader steps down after an election timeout) but
does not close it. The specification itself admits the violating state from `MCetcdraft`'s
initial state within `MCetcdraft.cfg`'s bounds, so model checking long enough finds it too. raft
v3.7.0 and `main` have the same specification.

**Reproduction:** `TestTLATraceStaleLeaderCompleteness` (raft's trace) and
`TestTLAModelStaleLeaderCompleteness` (the specification alone) in
[`issues/raft-tla-leader-completeness-stale-leader/tla_leader_completeness_test.go`](raft-tla-leader-completeness-stale-leader/tla_leader_completeness_test.go),
copied into the module root at etcd-io/raft@c51f010c851e (2026-10-23), go1.27.3 linux/arm64, with
`TLA_TOOLS` a directory holding what `validate.sh` downloads (`tla2tools.jar`, nightly 2.0
2026-11-06, and `CommunityModules-deps.jar`, as of 2026-11-08):

```
$ TLA_TOOLS=... go test -tags with_tla . -run '^TestTLA(Trace|Model)StaleLeaderCompleteness$' -count=1 -v
=== RUN   TestTLATraceStaleLeaderCompleteness
    tla_leader_completeness_test.go:57: Error: Invariant LeaderCompletenessInv is violated.
    ...
    tla_leader_completeness_test.go:59: Traceetcdraft rejects the trace of a correct raft run: exit status 12
--- FAIL: TestTLATraceStaleLeaderCompleteness (1.79s)
=== RUN   TestTLAModelStaleLeaderCompleteness
    tla_leader_completeness_test.go:382: replay: Error: Invariant LeaderCompletenessInv is violated.
    ...
    tla_leader_completeness_test.go:396: replay: also within MCetcdraft.cfg's limits (MCTimeout, MCSend, MCClientRequest)
    tla_leader_completeness_test.go:74: etcdraft.tla itself (from MCetcdraft's Init, 107 steps of NextAsync or stutter) reaches a state violating LeaderCompletenessInv
--- FAIL: TestTLAModelStaleLeaderCompleteness (5.10s)
```

The run: node 1 leads term 2 and appends an entry at index 4 that reaches no one; node 2 is elected
for term 3 with node 3's vote, appends its own entry at index 4, and hears nothing more (it stays
leader of term 3); node 1 is elected for term 4 with node 3's vote and commits index 5, and with it
index 4 (term 2). The invariant then asks node 2 (term 3 > 2) to hold node 1's index 4.

The second test replays the states of TLC's counterexample, the specification's variables only,
against `MCetcdraft.tla` from its `Init`, each step an action of `NextAsync` (a disjunct of `Next`)
or a stutter landing exactly on the next recorded state, with deadlock checking on, with and
without `MCetcdraft.cfg`'s limits: TLC reproduces every state and reports the invariant violated
at the last.

**Cause:** [`LeaderCompletenessInv`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/etcdraft.tla#L859-L869)
guards on `currentTerm[l] > entry.term`, the term the entry was created in, where leader
completeness needs the term it was committed in (here 4, after the stale leader's 3). The
specification has no variable recording the commit term.

## Proof

yes: the trace-check stage's statement (raft's traces conform to etcdraft.tla under upstream's trace validation) is false for runs with a stale leader; the stage's transcriptions check the guard `currentTerm[l] > entry.term /\ currentTerm[l] >= currentTerm[i]` instead (notes/trace-validation-plan.md, Q4).

## Fix

No fix branch. Either repair makes the test pass at `c51f010` (checked 2026-11-08 by patching
`tla/etcdraft.tla` in place):

- the guard `currentTerm[l] > entry.term /\ currentTerm[l] >= currentTerm[i]`: a server learns of a
  commit only in or after the commit's term, so a leader of a term at least the server's is the
  committing leader or a later one;
- #549's proposal, `\A server, leader : currentTerm[server] <= currentTerm[leader] =>
  IsPrefix(Committed(server), log[leader])`: the same guard without the entry-term condition (the
  entries it adds, of the leader's own term, are the leader's own).

The faithful repair records each entry's commit term (a history variable set when `commitIndex`
first covers it) and guards on it.

## Notes

Found 2026-11-08 by the trace-check stage's review (S4 round 2, N1), `TestGap7LeaderCompleteness` in
`examples/raft/tracecheck/gaps_test.go`. The replay uses `NextAsync` because evaluating the whole
of `Next` fails in some reachable states (`raft-tla-restart-truncated-log`); no recorded step is a
crash or a network fault. The replayed final state satisfies the first repair above, so that repair
is strictly weaker than the original on reachable states.
