---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#22483 issue open: the report (v3.7 leader sends MsgApp in reverse log order)
  - etcd-io/etcd#22485 pr open: the fix (keep marks, then collect in Ready order); verified in notes/pr-verify/etcd-22485.md on branch pr-verify/etcd-22485
  - etcd-io/etcd#22598 pr open: the regression test alone, for release-3.6 (passes there)
---

# `processMessages` returns the Ready's messages in reverse order

**Status**: a bug (a wrong result; performance and availability, not safety). raft emits
`Ready.Messages` in log order; etcd's raft loop sends them in the reverse order.

**Where**: `server/etcdserver/raft.go:357-401` at the pinned etcd revision (09669450f):
`(*raftNode).processMessages` walks `ms` from last to first (to keep only the newest
`MsgAppResp`) and appends each message it keeps (`raft.go:399`), so the result is the kept
messages reversed. Its callers send the result: `raft.go:242` (leader,
`r.transport.Send(r.processMessages(rd.Messages))`) and `raft.go:299` (follower). Introduced by
f3cea0a978 (#21810), kept in 4715a5474c (#21778); v3.6 cleared `To` on dropped messages and
returned the original slice, in order.

**What happens**: several `MsgApp` to one peer in one `Ready` (indexes 10, 11, 12) leave as 12,
11, 10. A follower rejects a `MsgApp` whose previous index it lacks; the leader lowers `Next` and
resends. Upstream reports each entry sent 2.5-3 times under sustained writes, full rafthttp send
buffers and about half v3.6's put rate (#22483). Reproduction:
`notes/pr-verify/etcd-22485/raft_order_test.go` (`TestProcessMessagesKeepsReadyOrder` of #22485):
copied into `server/etcdserver/` of the pinned fork revision, it fails (`got[0] is not the Ready
pointer`, `notes/pr-verify/etcd-22485/base.log`).

**Expected**: the kept messages in the `Ready`'s order (raft's contract for `Ready.Messages`,
and v3.6's behavior).

**How the proof handles it**: the spec on `lean`
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/raftNode__processMessages.lean`) states only that
the result's messages are valid ones (`rnMsgOk`), not their order, so the reverse order went
through; its doc comment records "in reverse order". Safety is unaffected (raft tolerates
reordered messages); the cost is liveness and throughput, which the proofs do not cover. On branch
`pr-verify/etcd-22485` the spec states the result exactly: the messages `rnKeepAt` keeps, in the
input's order (`rnKept`), for some per-index answers of `isIDRemoved`; it is proved of #22485's
code, and the pinned code does not meet it.

**Possible fixes**: #22485 (marks in a `[]bool` during the backward walk, then a forward pass
collecting the marked messages); equivalently, reverse the result before returning.

**Found**: 2026-10-17, verifying etcd-io/etcd#22485 (`etcd-pr-verify`); already reported upstream.
