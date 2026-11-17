---
upstream: none
checked: 2026-11-08
links:
  - etcd-io/raft#381 pr open: related, not this bug: a separate, lower-level specification (`tla/extended_spec/`) that models snapshot handling; it leaves `etcdraft.tla` as it is
blocks-proof: yes
---

# raft: TLA+ trace validation rejects a correct run where a follower installs a snapshot

When the leader sends a snapshot (`MsgSnap`) to a follower that has already committed some entries,
`tla/etcdraft.tla` handles it as an append request at index 1, below the follower's commit index,
and so changes neither the follower's log nor its commit index; raft installs the snapshot (or, if
the follower already has the snapshot's last entry, advances its commit index to it). Trace
validation (`tla/validate.sh` with `Traceetcdraft.tla`) therefore rejects the trace of a correct
three-node run at the leader's receipt of the follower's acknowledgement. Raft itself behaves
correctly: the follower installs the snapshot and catches up.

**Expected:** a trace of a correct run should pass `Traceetcdraft.tla`, as `tla/README.md`
describes: a failure "indicates a discrepancy between the model and its implementation".

**Impact:** every member of a bootstrapped cluster has committed its bootstrap configuration
entries, so any snapshot sent to a member that lags behind the leader's compacted log (the usual
reason a leader sends one) makes the trace fail. (A snapshot to a member added later, that has
committed nothing, is rejected too, for a separate reason:
[`raft-tla-snapshot-response-subtype`](raft-tla-snapshot-response-subtype.md).) Trace validation of
an application that compacts its log (etcd does) cannot check runs where a follower falls behind. raft v3.7.0 and
`main` have the same specification.

**Reproduction:** `TestTLATraceSnapshotToCommittedFollower` in
[`issues/raft-tla-snapshot-committed-follower/tla_snapshot_committed_follower_test.go`](raft-tla-snapshot-committed-follower/tla_snapshot_committed_follower_test.go),
copied into the module root at etcd-io/raft@c51f010c851e (2026-10-23), go1.27.3 linux/arm64, with
`TLA_TOOLS` a directory holding `validate.sh`'s `tla2tools.jar` (nightly 2.0, 2026-11-06) and
`CommunityModules-deps.jar` (downloaded 2026-11-08):

```
$ TLA_TOOLS=... go test -tags with_tla . -run '^TestTLATraceSnapshotToCommittedFollower$' -count=1 -v
    tla_snapshot_committed_follower_test.go:244: Error: Temporal property TraceMatched was violated.
    tla_snapshot_committed_follower_test.go:244: Error: The following behavior constitutes a counter-example:
    tla_snapshot_committed_follower_test.go:247: TLC matched lines 1-118 of 120; line 119: {"level":"debug","ts":1000000118,"msg":"trace","tag":"trace","event":{"name":"ReceiveAppendEntriesResponse","nid":"1","state":{"term":2,"vote":"1","commit":6},"role":"StateLeader","log":6,"conf":[["1","2","3"],[]],"msg":{"type":"MsgAppResp","term":2,"from":"3","to":"1","entries":0,"logTerm":0,"index":6,"commit":0,"vote":"0","reject":false,"rejectHint":0}}}
    tla_snapshot_committed_follower_test.go:249: Traceetcdraft rejects the trace of a correct raft run: exit status 12
--- FAIL: TestTLATraceSnapshotToCommittedFollower (0.77s)
```

The run (`RawNode`s configured as `tla/README.md`'s example, the test delivering messages): three
bootstrapped members; node 1 is elected for term 2, everything it sends node 3 after the election
is lost, and it commits indexes 4 to 6 with node 2; its application snapshots index 6 (configuration
{1, 2, 3}) and compacts its log. A heartbeat's response from node 3 (commit 3) makes the leader
send it the snapshot, which node 3 installs and acknowledges with index 6. In the specification
node 3 still has 3 entries and commit 3, and acknowledges 3, so no message matches line 119 (the
line still fails, on the index, with
[`raft-tla-snapshot-response-subtype`](raft-tla-snapshot-response-subtype.md)'s fix applied).

**Cause:** a `MsgSnap` is [`SendSnapshot`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/etcdraft.tla#L370-L371),
an append request with `mprevLogIndex = 0`, so it is handled at index 1.
[`ConflictAppendEntriesRequest` and `NoConflictAppendEntriesRequest`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/etcdraft.tla#L586-L600)
require `index > commitIndex[i]`, so for a follower with `commitIndex >= 1` only
[`AppendEntriesAlreadyDone`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/etcdraft.tla#L564-L584)
is enabled, which for a non-heartbeat changes nothing and acknowledges `commitIndex[i]`. Raft's
[`handleSnapshot`/`restore`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L1832-L1913)
ignores a snapshot only at or below its commit index; otherwise it fast-forwards its commit index
to the snapshot's index (when it has the snapshot's last entry) or replaces its log by the snapshot,
and acknowledges the new index.

## Proof

yes: the trace-check stage's statement (raft's traces conform to etcdraft.tla under upstream's trace validation) is false for runs that send a snapshot to a member that has committed any entry (notes/trace-validation-plan.md).

## Fix

No fix branch. [`fix.patch`](raft-tla-snapshot-committed-follower/fix.patch) (against `c51f010`)
gives snapshots their own handler in `AcceptAppendEntriesRequest`, following `raft.restore`: a
snapshot at or below the follower's commit index is ignored; when the follower has the snapshot's
last entry it commits up to it and keeps its log; otherwise its log becomes the snapshot's and it
commits all of it; it acknowledges `Max({commitIndex[i], Len(m.mentries)})` as an `"app"` response
(raft answers a snapshot with `MsgAppResp`). Since snapshots no longer reach
`AppendEntriesAlreadyDone`, the patch subsumes
[`raft-tla-snapshot-response-subtype`](raft-tla-snapshot-response-subtype.md)'s fix: the new handler
answers `"app"` itself, and with only that subtype fix this test still fails at line 119 (checked). The configuration is left to the `ApplyConfChange` event
raft logs while restoring. With it the test passes at `c51f010` (checked 2026-11-08 by applying it
to `tla/etcdraft.tla`). As a smoke test only, a 5-minute TLC simulation of `MCetcdraft`
(`-simulate -depth 60`) with the patch found no invariant violation (see Notes).

## Notes

Checks of the patch, 2026-11-08: 12 random runs with snapshots and configuration changes (this
repository's `examples/raft/tracecheck`, `FullConfig`, seeds 1-12, no restarts), validated by TLC:
9 rejected by the unpatched specification, all 12 accepted with this patch and
[`raft-tla-readded-member-matchindex`](raft-tla-readded-member-matchindex.md)'s applied together.
The smoke test: `tlc2.TLC -simulate -depth 60 -seed 1 -workers 2 -config MCetcdraft.cfg
MCetcdraft.tla` for 5 minutes, about 9.8 million states and 160,000 behaviors, no invariant
violation, patched or not.

Found 2026-11-08 by the trace-check stage's random runs with snapshots
(`examples/raft/tracecheck`, `FullConfig`); `notes/raft-trace-validation.md`, "Where etcdraft.tla
does not fit raft", item 3.
