---
upstream: none
checked: 2026-10-21
links:
  - etcd-io/raft#418 pr merged: related, flagged: added the 'treat m as immutable' comment on Step (etcd-io/raft@c1cf9fb); a reviewer found no in-repo path mutating m after Step, which this finding contradicts
  - etcd-io/raft#441 pr merged: related, not this bug: EnsureSnapshot/EnsureSnapshotMetadata no longer reassign non-nil fields, after a race found in etcd-io/etcd#21778 (ApplySnapshot writing its argument); EnsureConfState still writes AutoLeave
blocks-proof: no
---
# raft v3.7: `Step` writes into the caller's message and keeps it

In raft v3.7 (messages as pointers), `Step` writes the caller's message and keeps it: a follower
forwarding a proposal sets `m.To` to its leader and queues the same object in `Ready.Messages`;
read-index requests, forwarded messages and appended entries are kept by reference too.
`MemoryStorage.ApplySnapshot` and `handleSnapshot` fill nil fields of the caller's snapshot
(`EnsureSnapshot`). `Step`'s doc says only that callers must treat `m` as immutable after passing
it.

**Why not an issue:** documentation only: `Step`'s comment already forbids the caller from
touching `m` afterwards, and etcd steps freshly decoded messages it does not reuse
(INDEX-reviewed.md's Plan: "Non-issue, maybe some documentation change").

`TestStepWritesAndKeepsCallerMessage` in
[`nonissues/raft-step-writes-caller-message/step_writes_caller_message_test.go`](raft-step-writes-caller-message/step_writes_caller_message_test.go)
fails at etcd-io/raft@c51f010c851e, go1.27.3: `the caller's message was written: To = 2, want
unchanged 1` and `the caller's message is queued as an outgoing message`.

## Proof

no: the v3.7 design states it as ownership (`notes/raft-retarget-plan.md`, "Design"): `Step`
takes the message's cells and does not give them back, which etcd's use meets.

## Notes

A fix would document the transfer of ownership on `Step`/`RawNode.Step`/`Node.Step` and
`ApplySnapshot`, or `proto.Clone` what raft forwards or keeps. `Storage.Entries` refers to
"comments in Ready struct" that no longer exist.
