---
upstream: unchecked
checked: 2026-10-18
links:
candidate: issues/upstream/raft-readindex-removed-leader/
---

# raft: a read at a leader that alone is a quorum of a joint configuration waits for heartbeat responses

- **Status**: bug (liveness: a read index request is not answered although the leader's own acknowledgement is
  a quorum); found by the code review of the `raft-readindex-singleton-stale` fix (2026-10-18) and reproduced by a
  temporary test; fixed by the `IsSingleton(id)` change, in the `raft-readindex-removed-leader` candidate since the split (2026-10-18).
- **Where** (etcd-io/raft `main` 638f42739): `stepLeader`'s single-voter shortcut (`raft.go:1355-1361`) uses
  `IsSingleton()`, false for a joint configuration; the `ReadOnlySafe` path of `sendMsgReadIndexResponse`
  (`raft.go:2146-2162`) records the leader's own acknowledgement but decides only in the `MsgHeartbeatResp` handler.
- **What happens**: a leader of `{1}` applies a `ConfChangeV2` with an explicit transition that only adds a learner
  2: the configuration is `{1}&&{1}`, learners `{2}`. A read index request at the leader gets no read state until
  a heartbeat response arrives, which only the learner can send; with the learner unreachable, never (until the
  configuration leaves the joint state).
- **Expected**: answered at once (after the leader's first commit in its term), as at the single voter `{1}`.
- **How the proof handles it**: liveness; the proofs state safety only.
- **Possible fixes**: the candidate's guard, `IsSingleton(r.id)` (id is the only voter, via `Voters.VoteResult`); more
  generally, decide right after `recvAck(r.id, ...)` in the `ReadOnlySafe` path.
- **Found**: 2026-10-18, the code review of `fix/raft-readindex-singleton-stale`.
