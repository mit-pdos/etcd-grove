---
upstream: none
checked: 2026-11-08
links:
  - etcd-io/raft#381 pr open: related, not this bug: a separate, lower-level specification (`tla/extended_spec/`) that models snapshot handling; it leaves `etcdraft.tla` as it is
blocks-proof: yes
---

# raft: TLA+ trace validation rejects a correct run where a new member receives a snapshot

When the leader brings a newly added member up to date with a snapshot (`MsgSnap`), raft answers
with an append response (`MsgAppResp`), but `tla/etcdraft.tla` answers with a response of subtype
`"snapshot"`, which trace validation (`tla/validate.sh` with `Traceetcdraft.tla`) never matches to a
`MsgAppResp`. So the trace of a correct run, three members and a fourth added with an empty log, is
rejected when the leader receives the new member's acknowledgement. Raft itself behaves correctly:
the new member installs the snapshot and the leader records it as caught up.

**Expected:** a trace of a correct run should pass `Traceetcdraft.tla`, as `tla/README.md`
describes: a failure "indicates a discrepancy between the model and its implementation".

**Impact:** every snapshot a member acknowledges makes the trace fail, so trace validation of an
application that compacts its log (etcd does) cannot check runs where a member is added after the
leader compacted the entries it needs, the ordinary way a new member joins. raft v3.7.0 and `main`
have the same specification.

**Reproduction:** `TestTLATraceSnapshotToNewMember` in
[`issues/raft-tla-snapshot-response-subtype/tla_snapshot_response_subtype_test.go`](raft-tla-snapshot-response-subtype/tla_snapshot_response_subtype_test.go),
copied into the module root at etcd-io/raft@c51f010c851e (2026-10-23), go1.27.3 linux/arm64, with
`TLA_TOOLS` a directory holding `validate.sh`'s `tla2tools.jar` (nightly 2.0, 2026-11-06) and
`CommunityModules-deps.jar` (downloaded 2026-11-08):

```
$ TLA_TOOLS=... go test -tags with_tla . -run '^TestTLATraceSnapshotToNewMember$' -count=1 -v
    tla_snapshot_response_subtype_test.go:236: Error: Temporal property TraceMatched was violated.
    tla_snapshot_response_subtype_test.go:236: Error: The following behavior constitutes a counter-example:
    tla_snapshot_response_subtype_test.go:239: TLC matched lines 1-127 of 129; line 128: {"level":"debug","ts":1000000127,"msg":"trace","tag":"trace","event":{"name":"ReceiveAppendEntriesResponse","nid":"1","state":{"term":2,"vote":"1","commit":5},"role":"StateLeader","log":5,"conf":[["1","2","3","4"],[]],"msg":{"type":"MsgAppResp","term":2,"from":"4","to":"1","entries":0,"logTerm":0,"index":5,"commit":0,"vote":"0","reject":false,"rejectHint":0}}}
    tla_snapshot_response_subtype_test.go:241: Traceetcdraft rejects the trace of a correct raft run: exit status 12
--- FAIL: TestTLATraceSnapshotToNewMember (1.80s)
```

The run (`RawNode`s configured as `tla/README.md`'s example, the test delivering messages): three
bootstrapped members and a fourth `RawNode` with empty storage and no bootstrap; node 1 is elected
for term 2 and adds node 4 (`ConfChangeAddNode`, index 5); once that is applied, its application
snapshots index 5 (configuration {1, 2, 3, 4}) and compacts its log. Node 4 rejects the leader's
first append, receives the snapshot, installs it and acknowledges index 5. The specification follows
the snapshot (node 4's log and commit index become 5) and its response has the right index, but its
subtype is `"snapshot"`, so no message matches line 128.

**Cause:** [`AppendEntriesAlreadyDone`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/etcdraft.tla#L576-L583)
replies with `msubtype |-> m.msubtype`, `"snapshot"` for a snapshot, while raft's
[`handleSnapshot`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L1832-L1847)
answers with `MsgAppResp`, which `Traceetcdraft.tla` maps to subtype `"app"`
([`RaftMsgSubtype`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/Traceetcdraft.tla#L26-L29))
and requires of the received message
([`LoglineIsAppendEntriesResponse`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/Traceetcdraft.tla#L163-L171)).

## Proof

yes: the trace-check stage's statement (raft's traces conform to etcdraft.tla under upstream's trace validation) is false for runs where a member acknowledges a snapshot (notes/trace-validation-plan.md).

## Fix

No fix branch. [`fix.patch`](raft-tla-snapshot-response-subtype/fix.patch) (against `c51f010`)
makes `AppendEntriesAlreadyDone` answer a snapshot with subtype `"app"`, as raft does. With it the
test passes at `c51f010` (checked 2026-11-08 by applying it to `tla/etcdraft.tla`).

## Notes

This fix alone does not make snapshots to a member that has already committed entries (every
bootstrapped member) pass: the specification then does not install the snapshot at all
([`raft-tla-snapshot-committed-follower`](raft-tla-snapshot-committed-follower.md), whose patch
handles snapshots separately and answers `"app"` too, so it subsumes this one). Of 12 random runs
with snapshots and configuration changes (this repository's `examples/raft/tracecheck`,
`FullConfig`), seed 3 is rejected by the unpatched specification at a new member's snapshot
acknowledgement and accepted with this fix alone. Found 2026-11-08 while writing up
`raft-tla-snapshot-committed-follower`.
