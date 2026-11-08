---
upstream: none
checked: 2026-11-08
links:
  - etcd-io/raft#226 pr open: related, reworks the trace specification's restart and moves the ApplyConfChange trace out of switchToConfig; leaves InitState logged before the persisted state is loaded
  - etcd-io/raft#549 issue open: related, another etcdraft.tla finding (LeaderCompletenessInv)
blocks-proof: yes
---

# raft: trace logging records `InitState` before the persisted state is loaded, so TLA+ trace validation rejects every restart

With the `with_tla` build tag, a node restarted from its storage (`RestartNode`, or `NewRawNode` on
a non-empty `Storage`) logs its `InitState` event before it loads its hard state and configuration:
the event says term 0, vote 0, an empty configuration. Trace validation (`tla/validate.sh` with
`Traceetcdraft.tla`) matches an `InitState` after the start of the trace to a restart and checks it
against the persisted state, so it rejects the trace of any run with a restart. raft itself behaves
correctly: the restarted node has its persisted term, vote, commit index and configuration.

**Expected:** a trace of a correct run with a restart should pass `Traceetcdraft.tla`, as
`tla/README.md` describes ("The `StartNode` and/or `RestartNode` should be invoked with `Config`
with `TraceLogger` property set"; a failure "indicates a discrepancy between the model and its
implementation"); the `InitState` event should record the state the node starts in.

**Impact:** trace validation of any application that restarts a node (any process restart, the
case `etcdraft.tla`'s `Restart` models) fails with no bug in raft, at the restarted node's first
event; the rest of the trace is never checked. Traces that start every node fresh are unaffected
(their first `InitState` is a bootstrap line, not validated). raft v3.7.0 and `main` log the same.

**Reproduction:** `TestTLATraceRestart` in
[`issues/raft-tla-restart-initstate-unmatched/tla_restart_test.go`](raft-tla-restart-initstate-unmatched/tla_restart_test.go),
copied into the module root at etcd-io/raft@c51f010c851e (2026-10-23), go1.27.3 linux/arm64, with
`TLA_TOOLS` a directory holding `validate.sh`'s `tla2tools.jar` (nightly 2.0, 2026-11-06) and
`CommunityModules-deps.jar` (as downloaded 2026-11-08):

```
$ TLA_TOOLS=... go test -tags with_tla . -run '^TestTLATraceRestart$' -count=1 -v
    tla_restart_test.go:221: Error: Temporal property TraceMatched was violated.
    tla_restart_test.go:221: Error: The following behavior constitutes a counter-example:
    tla_restart_test.go:224: no behavior matches trace line 82: {"level":"debug","ts":1000000081,"msg":"trace","tag":"trace","event":{"name":"InitState","nid":"2","state":{"term":0,"vote":"0","commit":4},"role":"StateFollower","log":4,"conf":[[],[]]}}
    tla_restart_test.go:226: Traceetcdraft rejects the trace of a correct raft run: exit status 12
--- FAIL: TestTLATraceRestart (0.83s)
```

The run: three nodes configured as `tla/README.md`'s example; node 1 is elected for term 2 and
commits its entry at index 4 on every node; node 2 snapshots index 4 with its configuration and is
restarted (a new `RawNode` on the same `MemoryStorage`, as `RestartNode` does); the test checks it
restarted with term 2, vote 1, commit 4 and voters 1, 2, 3, then lets it answer a heartbeat. Its
`InitState` line says term 0 and no voters (its commit, 4, is only the snapshot's index, which
the log starts from).

**Cause:** [`newRaft`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L466-L487)
calls `traceInitState` right after building the `raft` struct, before `confchange.Restore` and
`loadState`. [`RestartIfLogged`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/Traceetcdraft.tla#L361-L364)
takes an `InitState` line as `Restart(i)` (term, vote, commit, log and configuration from the
node's durable state) and checks it with `ValidatePostStates(i)`, which the logged term 0 and
empty configuration fail. Logging `InitState` later is not enough on its own: `newRaft` then calls
`becomeFollower`, which logs a `BecomeFollower` that
[`StepDownToFollowerIfLogged`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/Traceetcdraft.tla#L380-L384)
matches only for a leader or candidate, while the restarted node is already a follower.

## Proof

yes: the trace-check stage's statement (raft's traces conform to etcdraft.tla under upstream's trace validation) is false for runs that restart a node (notes/trace-validation-plan.md).

## Fix

No fix branch. [`fix.patch`](raft-tla-restart-initstate-unmatched/fix.patch) (against `c51f010`)
makes `newRaft` trace only the state it returns: it sets `traceLogger` once the persisted state is
loaded and the node is a follower, then logs `InitState`, so restoring the configuration
(`ApplyConfChange`) and the initial `becomeFollower` are not logged as transitions. With it
`TestTLATraceRestart` passes, and `go test ./...` passes with and without `-tags with_tla`
(checked 2026-11-08). A fresh node's trace changes from `InitState`, `BecomeFollower` (both at term
0) to one `InitState` at term 0; `Bootstrap` still logs its `BecomeFollower` and `ApplyConfChange`
lines, all bootstrap lines of `Traceetcdraft.tla`.

**If a reviewer asks**: moving only `traceInitState` after `loadState` (keeping the
`BecomeFollower` it is followed by) makes the `InitState` line match and the test fail at the next
line, that `BecomeFollower` (checked). The specification could instead skip a `BecomeFollower` right
after an `InitState`, but the trace would still say the restart passed through an empty state.

## Notes

The test snapshots before the restart because `Restart` restores the configuration from the
durable state, which raft's storage holds only in a snapshot's `ConfState`; an application that
re-applies configuration entries after its snapshot would meet a different mismatch. Found
2026-11-08 by the trace-check stage's random runs with restarts (`examples/raft/tracecheck/sim.go`,
`Config.Restarts`; `notes/raft-trace-validation.md`, "Where etcdraft.tla does not fit raft", item 1).
