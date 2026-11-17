---
upstream: none
checked: 2026-11-08
links:
  - etcd-io/raft#381 pr open: related, the extended TLA+ specification keeps the same AddLearner guard (no demotion)
  - etcd-io/raft#549 issue open: related, another etcdraft.tla finding (LeaderCompletenessInv)
blocks-proof: yes
---

# raft: TLA+ trace validation rejects demoting a voter to a learner

raft accepts a `ConfChangeAddLearnerNode` for a node that is a voter: the voter becomes a learner
(a demotion), with the simple protocol when nothing else changes. `tla/etcdraft.tla`'s
`AddLearner` only adds a node that is neither a voter nor a learner, so trace validation
(`tla/validate.sh` with `Traceetcdraft.tla`) rejects the trace of a correct three-node run that
demotes a voter, at the leader's proposal. raft itself behaves correctly: the change commits and
every node applies it.

**Expected:** a trace of a correct run should pass `Traceetcdraft.tla`, as `tla/README.md`
describes (a failure "indicates a discrepancy between the model and its implementation"); raft
supports demotion ([`makeLearner`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/confchange/confchange.go#L191-L228):
"we either add a new learner or demote a voter"; `Config.StepDownOnRemoval`: a leader "removed from
the group or demoted to a learner").

**Impact:** trace validation of an application that demotes voters fails with no bug in raft, at
the demotion's `ChangeConf` event; the rest of the trace is never checked. etcd itself does not
demote members (its membership API removes, adds and promotes), so etcd's own traces do not reach
it; other users of the raft library that move voters to learners do. raft v3.7.0 and `main` have
the same specification.

**Reproduction:** `TestTLATraceLearnerDemotion` in
[`issues/raft-tla-learner-demotion-unmodelled/tla_learner_demotion_test.go`](raft-tla-learner-demotion-unmodelled/tla_learner_demotion_test.go),
copied into the module root at etcd-io/raft@c51f010c851e (2026-10-23), go1.27.3 linux/arm64, with
`TLA_TOOLS` a directory holding `validate.sh`'s `tla2tools.jar` (nightly 2.0, 2026-11-06) and
`CommunityModules-deps.jar` (as downloaded 2026-11-08):

```
$ TLA_TOOLS=... go test -tags with_tla . -run '^TestTLATraceLearnerDemotion$' -count=1 -v
    tla_learner_demotion_test.go:176: Error: Temporal property TraceMatched was violated.
    tla_learner_demotion_test.go:176: Error: The following behavior constitutes a counter-example:
    tla_learner_demotion_test.go:179: no behavior matches trace line 80: {"level":"debug","ts":1000000079,"msg":"trace","tag":"trace","event":{"name":"ChangeConf","nid":"1","state":{"term":2,"vote":"1","commit":4},"role":"StateLeader","log":4,"conf":[["1","2","3"],[]],"prop":{"cc":{"changes":[{"nid":"3","action":"AddLearner"}]}}}}
    tla_learner_demotion_test.go:181: Traceetcdraft rejects the trace of a correct raft run: exit status 12
--- FAIL: TestTLATraceLearnerDemotion (0.81s)
```

The run: three nodes configured as `tla/README.md`'s example, every message delivered in order;
node 1 is elected for term 2 and proposes `ConfChangeAddLearnerNode` of node 3
(`ProposeConfChange`); the entry commits at index 5 and each node applies it (`ApplyConfChange`).
The test checks that every node then has commit 5, voters 1 and 2 and learner 3.

**Cause:** [`AddLearner(i, j)`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/etcdraft.tla#L439-L449)
requires `j \notin GetConfig(i) \union GetLearners(i)` and keeps the voters unchanged (`newconf |->
GetConfig(i)`), so no step of the specification matches a leader proposing to make a voter a
learner; [`AddLearnerIfLogged`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/Traceetcdraft.tla#L338-L343)
maps every `AddLearner` change in the trace to it.

## Proof

yes: the trace-check stage's statement (raft's traces conform to etcdraft.tla under upstream's trace validation) is false for runs that demote a voter to a learner (notes/trace-validation-plan.md).

## Fix

No fix branch, and no patch: whether the specification should model demotion is a modelling
decision for its maintainers. Modelling it would make `AddLearner` accept a voter, `j \notin
GetLearners(i)`, and remove it from the voters of the configuration it appends, `newconf |->
GetConfig(i) \ {j}` (a no-op change for a new learner). With exactly that change to
`tla/etcdraft.tla` at `c51f010`, `TestTLATraceLearnerDemotion` passes, invariants included (checked
2026-11-08); `MCetcdraft` was not model-checked with it. The model would also have to decide what a
demoted leader does (raft keeps leading unless `StepDownOnRemoval` is set). Otherwise, `tla/README.md` could say that traces with demotions
are not supported.

## Notes

Found 2026-11-08 by the trace-check stage's random runs with configuration changes
(`examples/raft/tracecheck/sim.go`, `FullConfig`, whose proposals now avoid demotion;
`notes/raft-trace-validation.md`, "Where etcdraft.tla does not fit raft", item 2).
