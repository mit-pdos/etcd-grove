---
upstream: none
checked: 2026-11-08
links:
  - etcd-io/raft#381 pr open: related, a separate extended specification; it sends the leader's commit index in an empty append request but still clamps it in a non-empty one, so it has the same mismatch for a cut batch
blocks-proof: yes
---

# raft: TLA+ trace validation rejects a correct run in which an append request stops short of the commit index

When the leader sends a follower an append request (`MsgApp`) whose entries end before the leader's
commit index, raft puts the leader's whole commit index in the message, and the follower commits
only up to the last entry it received. `tla/etcdraft.tla` instead sends the commit index clamped to
the last entry sent, so trace validation (`tla/validate.sh` with `Traceetcdraft.tla`) rejects the
trace of a correct three-node run at that message. Raft itself behaves correctly; the specification
does not describe what it sends.

**Expected:** a trace of a correct run should pass `Traceetcdraft.tla`, as `tla/README.md`
describes: a failure "indicates a discrepancy between the model and its implementation".

**Impact:** trace validation of any application in which a follower falls behind the leader's
commit index by more than one `MsgApp` can carry: a batch cut by `MaxSizePerMsg` (etcd uses 1 MiB, `server/etcdserver/raft.go`,
so a follower catching up after a partition or restart, or a new member, reaches it), or the empty
`MsgApp` a throttled follower in `StateReplicate` gets when its inflight window is full. Such traces
fail validation with no bug in raft. raft v3.7.0 and `main` have the same specification and code.

**Reproduction:** `TestTLATraceMsgAppCommitBeyondEntries` in
[`issues/raft-tla-msgapp-commit-unclamped/tla_msgapp_commit_test.go`](raft-tla-msgapp-commit-unclamped/tla_msgapp_commit_test.go),
copied into the module root at etcd-io/raft@c51f010c851e (2026-10-23), go1.27.3 linux/arm64, with
`TLA_TOOLS` a directory holding the TLA+ tools `validate.sh` fetches (`tla2tools.jar` nightly 2.0
2026-11-06 and `CommunityModules-deps.jar` as downloaded 2026-11-08):

```
$ TLA_TOOLS=... go test -tags with_tla . -run '^TestTLATraceMsgAppCommitBeyondEntries$' -count=1 -v
    tla_msgapp_commit_test.go:206: Error: Temporal property TraceMatched was violated.
    tla_msgapp_commit_test.go:206: Error: The following behavior constitutes a counter-example:
    tla_msgapp_commit_test.go:208: Traceetcdraft rejects the trace of a correct raft run: exit status 12
--- FAIL: TestTLATraceMsgAppCommitBeyondEntries (0.66s)
```

The run, with `MaxSizePerMsg` 1 (every `MsgApp` carries one entry): node 1 leads term 2; its first
`MsgApp` to node 3 is lost; node 2 receives indexes 4 to 6 and node 1 commits 6. Node 3 answers a
heartbeat, and node 1 resends from index 4: one entry, commit 6. Node 3 commits 4. The trace is
matched up to the line before that `MsgApp` (line 89 of 93; with `MAX_TRACE=88` it passes), where
the specification can only send commit 4.

**Cause:** [`maybeSendAppend`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/raft.go#L651-L658)
sends `Commit: r.raftLog.committed` whatever entries the message carries, and the follower clamps it
([`maybeAppend`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/log.go#L129):
`commitTo(min(committed, lastnewi))`). [`AppendEntriesInRangeToPeer`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/etcdraft.tla#L339)
sends `Min({commitIndex[i], lastEntry})`, and `Traceetcdraft.tla` checks the message's commit index
against the logged one
([`LoglineIsAppendEntriesRequest`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/Traceetcdraft.tla#L158)).
The two agree only when the message reaches the leader's commit index.

## Proof

yes: the trace-check stage's statement (raft's traces conform to etcdraft.tla under upstream's trace validation) is false for runs that send a `MsgApp` ending before the leader's commit index (a batch cut by `MaxSizePerMsg`, or a throttled follower's empty `MsgApp`) (notes/trace-validation-plan.md).

## Fix

No fix branch. [`fix.patch`](raft-tla-msgapp-commit-unclamped/fix.patch) (against `c51f010`) sends
the leader's commit index in an append request, as raft does; the receiver already clamps it
([`AppendEntriesAlreadyDone`](https://github.com/etcd-io/raft/blob/c51f010c851edd0dada5af41bafbf68e54617767/tla/etcdraft.tla#L575):
`CommitTo(i, Min({m.mcommitIndex, m.mprevLogIndex+Len(m.mentries)}))`). Heartbeats keep
`Min(commitIndex, matchIndex)` and snapshots the snapshot's index (`Traceetcdraft.tla` does not check
a snapshot's commit index). With the patch applied to `tla/etcdraft.tla`, the test passes, and
`tla/example.ndjson` still validates (checked 2026-11-08).

## Notes

The follower side of the specification needs no change: it never commits past what it received.
Found 2026-11-08 by the trace-check stage's review of Draft S4 (case analysis), then witnessed with
the concurrent harness at `MaxInflightMsgs: 1` (`notes/raft-trace-validation.md`, item 5); the
deterministic schedule above was written for this report (`examples/raft/tracecheck/gaps_test.go`
has none for item 5).
