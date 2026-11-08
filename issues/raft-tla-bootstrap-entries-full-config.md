---
upstream: none
checked: 2026-11-08
links: []
blocks-proof: yes
---

# raft: TLA+ trace validation rejects a new member that applies the bootstrap entries one at a time

`RawNode.Bootstrap` appends one `ConfChangeAddNode` entry per peer, so the bootstrap log of a
three-node cluster holds configurations {1}, {1, 2} and {1, 2, 3}. `tla/Traceetcdraft.tla`'s
initial log (`TraceInitLogVars`) instead gives every bootstrap entry the whole configuration
{1, 2, 3}. A member added later that receives the bootstrap entries separately (one entry per
append request, `MaxSizePerMsg` small) commits and applies entry 1 alone, and raft gives it the
configuration {1}; the specification gives it {1, 2, 3}, so trace validation (`tla/validate.sh`
with `Traceetcdraft.tla`) rejects the trace at the member's next receipt. Raft itself behaves
correctly: the member applies the three entries in turn, then its own addition, and ends with
voters 1, 2, 3, 4.

**Expected:** a trace of a correct run should pass `Traceetcdraft.tla`, as `tla/README.md`
describes: a failure "indicates a discrepancy between the model and its implementation".
`MCetcdraft.tla`'s own `BootstrapLog` builds the bootstrap entries incrementally, as raft does.

**Impact:** trace validation of a run in which a member added after bootstrap, before the leader
compacted its bootstrap entries, receives them in separate append requests: with `MaxSizePerMsg`
small enough to cut the bootstrap entries apart (etcd's 1 MiB never does). At `c51f010` such a
trace is rejected earlier, at the leader's append request carrying one entry
([`raft-tla-msgapp-commit-unclamped`](raft-tla-msgapp-commit-unclamped.md)); with that fixed, it
is rejected here. raft v3.7.0 and `main` have the same specification.

**Reproduction:** `TestTLATraceBootstrapEntriesOneByOne` in
[`issues/raft-tla-bootstrap-entries-full-config/tla_bootstrap_entries_test.go`](raft-tla-bootstrap-entries-full-config/tla_bootstrap_entries_test.go),
copied into the module root at etcd-io/raft@c51f010c851e (2026-10-23), go1.27.3 linux/arm64, with
`TLA_TOOLS` a directory holding `validate.sh`'s `tla2tools.jar` (nightly 2.0, 2026-11-06) and
`CommunityModules-deps.jar` (as downloaded 2026-11-08). At `c51f010` it fails at line 128, the
leader's one-entry `MsgApp` (the earlier finding); with that finding's `fix.patch` applied:

```
$ git apply issues/raft-tla-msgapp-commit-unclamped/fix.patch
$ TLA_TOOLS=... go test -tags with_tla . -run '^TestTLATraceBootstrapEntriesOneByOne$' -count=1 -v
    tla_bootstrap_entries_test.go:176: Error: Temporal property TraceMatched was violated.
    tla_bootstrap_entries_test.go:176: Error: The following behavior constitutes a counter-example:
    tla_bootstrap_entries_test.go:184: no behavior matches trace line 141: {"level":"debug","ts":1000000140,"msg":"trace","tag":"trace","event":{"name":"ReceiveAppendEntriesRequest","nid":"4","state":{"term":2,"vote":"0","commit":1},"role":"StateFollower","log":1,"conf":[["1"],[]],"msg":{"type":"MsgApp","term":2,"from":"1","to":...
    tla_bootstrap_entries_test.go:186: Traceetcdraft rejects the trace of a correct raft run: exit status 12
--- FAIL: TestTLATraceBootstrapEntriesOneByOne (0.98s)
```

The run: three bootstrapped nodes and a fourth with an empty log, `MaxSizePerMsg` 1, every message
delivered in order; node 1 is elected for term 2 and adds node 4 (`ConfChangeAddNode`, index 5);
node 4 receives indexes 1 to 5 one per append request, and the test checks it applied the
configurations [1], [1 2], [1 2 3], [1 2 3 4] and has commit 5.

**Cause:** [`TraceInitLogVars`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/Traceetcdraft.tla#L82)
gives each of the `log` bootstrap entries `newconf |-> BootstrappedConfig(i)`, the configuration of
the last bootstrap line; [`ApplySimpleConfChange`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/etcdraft.tla#L464-L475)
then applies entry 1 as {1, 2, 3}, which the member's next line (`conf` [[1]]) contradicts.

## Proof

yes: the trace-check stage's statement (raft's traces conform to etcdraft.tla under upstream's trace validation) is false for runs in which a new member applies the bootstrap entries separately (notes/trace-validation-plan.md).

## Fix

No fix branch. [`fix.patch`](raft-tla-bootstrap-entries-full-config/fix.patch) (against
`c51f010`, `tla/Traceetcdraft.tla` only) gives bootstrap entry `j` the configuration of the `j`-th
bootstrap `ApplyConfChange` line of its server (raft logs `{1}`, `{1, 2}`, `{1, 2, 3}`), ignoring
the configuration-less `ApplyConfChange` older raft logged when restoring (`tla/example.ndjson` has
them). With it and `raft-tla-msgapp-commit-unclamped`'s `fix.patch` the test passes (checked
2026-11-08).

## Notes

Found 2026-11-08 by the mutation testing of the corrected specification (`etc/tla-fixes/`): a
control mutant (a leader that appends no empty entry) made it frequent; then reproduced with
unmodified raft.
