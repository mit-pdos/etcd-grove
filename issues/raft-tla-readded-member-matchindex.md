---
upstream: none
checked: 2026-11-08
links:
  - etcd-io/raft#381 pr open: related, not this bug: a separate, lower-level specification (`tla/extended_spec/`) that models the leader's progress tracking; it leaves `etcdraft.tla` as it is
blocks-proof: yes
---

# raft: TLA+ trace validation rejects a correct run where a removed member is added back

When the leader removes a member and later adds it back, raft starts the member over with a fresh
progress (match index 0), so the leader's heartbeats to it carry commit index 0 until it
acknowledges an append. `tla/etcdraft.tla` keeps the leader's `matchIndex` for the member from
before the removal and expects the heartbeat to carry `Min(commitIndex, matchIndex)`, so trace
validation (`tla/validate.sh` with `Traceetcdraft.tla`) rejects the trace of a correct three-node
run at that heartbeat. Raft itself behaves correctly: the member answers and is brought up to date.

**Expected:** a trace of a correct run should pass `Traceetcdraft.tla`, as `tla/README.md`
describes: a failure "indicates a discrepancy between the model and its implementation".

**Impact:** trace validation of an application that removes a member and adds the same ID back
fails as soon as the leader sends the re-added member a heartbeat before the member has
acknowledged an append (a lost or delayed append is enough). etcd itself never re-adds a removed ID (it
gives every new member a new ID and refuses a removed one), but raft allows it, other applications
of raft can do it, and `etcdraft.tla`'s `DeleteServer` and `AddNewServer` model it, so model
checking explores it too. raft v3.7.0 and `main` have the same specification.

**Reproduction:** `TestTLATraceReaddedMemberHeartbeat` in
[`issues/raft-tla-readded-member-matchindex/tla_readded_member_matchindex_test.go`](raft-tla-readded-member-matchindex/tla_readded_member_matchindex_test.go),
copied into the module root at etcd-io/raft@c51f010c851e (2026-10-23), go1.27.3 linux/arm64, with
`TLA_TOOLS` a directory holding `validate.sh`'s `tla2tools.jar` (nightly 2.0, 2026-11-06) and
`CommunityModules-deps.jar` (downloaded 2026-11-08):

```
$ TLA_TOOLS=... go test -tags with_tla . -run '^TestTLATraceReaddedMemberHeartbeat$' -count=1 -v
    tla_readded_member_matchindex_test.go:245: Error: Temporal property TraceMatched was violated.
    tla_readded_member_matchindex_test.go:245: Error: The following behavior constitutes a counter-example:
    tla_readded_member_matchindex_test.go:248: TLC matched lines 1-159 of 177; line 160: {"level":"debug","ts":1000000159,"msg":"trace","tag":"trace","event":{"name":"SendAppendEntriesRequest","nid":"1","state":{"term":2,"vote":"1","commit":7},"role":"StateLeader","log":7,"conf":[["1","2","3"],[]],"msg":{"type":"MsgHeartbeat","term":2,"from":"1","to":"3","entries":0,"logTerm":0,"index":0,"commit":0,"vote":"0","reject":false,"rejectHint":0}}}
    tla_readded_member_matchindex_test.go:250: Traceetcdraft rejects the trace of a correct raft run: exit status 12
--- FAIL: TestTLATraceReaddedMemberHeartbeat (1.06s)
```

The run (`RawNode`s configured as `tla/README.md`'s example, the test delivering messages): three
bootstrapped members; node 1 is elected for term 2 and replicates index 5 to both followers (its
match index for node 3 is 5); it proposes `ConfChangeRemoveNode` of node 3 (index 6), which is
committed and applied, then `ConfChangeAddNode` of node 3 (index 7), committed with node 2 and
applied. The append the leader then sends node 3 is lost; its next heartbeat to node 3 carries
commit `min(Match 0, committed 7) = 0`, where the specification expects `Min(7, 5) = 5`.

**Cause:** [`ApplySimpleConfChange`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/etcdraft.tla#L464-L475)
leaves `matchIndex` unchanged, so a server the new configuration drops keeps its entry, which
[`AppendEntriesInRangeToPeer`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/etcdraft.tla#L339)
uses for a heartbeat's commit index once the server is added back. Raft
[deletes a removed member's progress](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/confchange/confchange.go#L231-L244)
and [creates a fresh one with `Match: 0`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/confchange/confchange.go#L247-L271)
when it is added again, and [`sendHeartbeat`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L694-L708)
sends `min(pr.Match, committed)`.

## Proof

yes: the trace-check stage's statement (raft's traces conform to etcdraft.tla under upstream's trace validation) is false for runs that remove a member and add it back (notes/trace-validation-plan.md).

## Fix

No fix branch. [`fix.patch`](raft-tla-readded-member-matchindex/fix.patch) (against `c51f010`)
resets, in `ApplySimpleConfChange`, `matchIndex[i][j]` to 0 for every server `j` that the applied
configuration (its voters and learners) does not contain, as raft drops its progress then. With it
the test passes at `c51f010` (checked 2026-11-08 by applying it to `tla/etcdraft.tla`). As a smoke
test only, a 5-minute TLC simulation of `MCetcdraft` (`-simulate -depth 60`) with the patch found
no invariant violation (see Notes).

## Notes

Checks of the patch, 2026-11-08: 12 random runs with snapshots and configuration changes (this
repository's `examples/raft/tracecheck`, `FullConfig`, seeds 1-12, no restarts), validated by TLC:
9 rejected by the unpatched specification, all 12 accepted with this patch and
[`raft-tla-snapshot-committed-follower`](raft-tla-snapshot-committed-follower.md)'s applied together.
The smoke test: `tlc2.TLC -simulate -depth 60 -seed 1 -workers 2 -config MCetcdraft.cfg
MCetcdraft.tla` for 5 minutes, about 8 million states and 130,000 behaviors, no invariant
violation (the unpatched specification, the same run: none either).

Found 2026-11-08 by the trace-check stage's random runs with configuration changes
(`examples/raft/tracecheck`, `FullConfig`); `notes/raft-trace-validation.md`, "Where etcdraft.tla
does not fit raft", item 4.
