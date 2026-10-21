---
upstream: none
checked: 2026-10-21
links:
  - etcd-io/raft#536 pr merged: related, not this bug: the removed-leader fix; its first version (`IsSingleton(id)`, via `VoteResult`) also fixed this, the merged form (`IsVoter(r.id) && IsSingleton()`, after review) does not, so `{1}&&{1}` still waits
  - etcd-io/raft#535 pr merged: related, not this bug: moved the single-voter shortcut into `sendMsgReadIndexResponse` (the singleton-stale fix), still `IsSingleton()`
---

# raft: a read at a leader that alone is a quorum of a joint configuration waits for heartbeat responses

- **Status**: bug (liveness: a read index request is not answered although the leader's own acknowledgement is
  a quorum); found by the code review of the `raft-readindex-singleton-stale` fix (2026-10-18) and reproduced by a
  temporary test. Not fixed upstream: the `IsSingleton(id)` change of the `raft-readindex-removed-leader` candidate
  fixed it, but the fix merged as etcd-io/raft#536 is the reviewer's `IsVoter(r.id) && IsSingleton()`, which leaves
  `{1}&&{1}` waiting (2026-10-19).
- **Where** (etcd-io/raft `main` 638f42739): `stepLeader`'s single-voter shortcut (`raft.go:1355-1361`) uses
  `IsSingleton()`, false for a joint configuration; the `ReadOnlySafe` path of `sendMsgReadIndexResponse`
  (`raft.go:2146-2162`) records the leader's own acknowledgement but decides only in the `MsgHeartbeatResp` handler.
- **What happens**: a leader of `{1}` applies a `ConfChangeV2` with an explicit transition that only adds a learner
  2: the configuration is `{1}&&{1}`, learners `{2}`. A read index request at the leader gets no read state until
  a heartbeat response arrives, which only the learner can send; with the learner unreachable, never (until the
  configuration leaves the joint state).
- **Expected**: answered at once (after the leader's first commit in its term), as at the single voter `{1}`.
- **How the proof handles it**: liveness; the proofs state safety only.
- **Possible fixes**: the candidate's first guard, `IsSingleton(r.id)` (id is the only voter, via `Voters.VoteResult`); more
  generally, decide right after `recvAck(r.id, ...)` in the `ReadOnlySafe` path.
- **Found**: 2026-10-18, the code review of `fix/raft-readindex-singleton-stale`.
