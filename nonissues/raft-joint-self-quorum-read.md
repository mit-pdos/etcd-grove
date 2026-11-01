---
upstream: none
checked: 2026-11-01
links:
  - etcd-io/raft#536 pr merged: related, not this bug: the removed-leader fix; its first version (`IsSingleton(id)`, via `VoteResult`) also fixed this, the merged form (`IsVoter(r.id) && IsSingleton()`, after review) does not
  - etcd-io/raft#535 pr merged: related, not this bug: moved the single-voter shortcut into `sendMsgReadIndexResponse`, still `IsSingleton()`
blocks-proof: no
---
# raft: a read at a leader that alone is a quorum of a joint configuration waits for a learner's heartbeat response

A leader of `{1}` that adds a learner 2 through an explicit joint transition is in the joint
configuration `{1}&&{1}`, of which it alone is a quorum; a `ReadOnlySafe` read index request there
is not answered until a heartbeat response arrives, which only the learner can send. With the
learner unreachable, the read is never answered, not even after the configuration leaves the joint
state (a read issued after that is answered at once).

**Why not an issue:** not a guarantee raft makes (no bound on when a read is answered; it is
answered as soon as the learner responds), in a configuration etcd never enters (etcd proposes only
v1 conf changes, never joint ones), and a read retried after the joint state is answered at once;
INDEX-reviewed.md's Plan: "Skip for now".

`TestRawNodeReadIndexJointSelfQuorum` in
[`nonissues/raft-joint-self-quorum-read/joint_self_quorum_read_test.go`](raft-joint-self-quorum-read/joint_self_quorum_read_test.go)
(public `RawNode` API) fails at etcd-io/raft@c51f010c851e, go1.27.3: `Error: Should be true` /
`no read state for a read at a leader that alone is a quorum of voters=(1)&&(1) learners=(2)`.

## Proof

no: liveness; the proofs state safety only.

## Notes

The fix would be the first version of #536's guard, `Voters.VoteResult({r.id: true}) == VoteWon`
in place of `IsVoter(r.id) && IsSingleton()`, or deciding right after the leader's own `recvAck`
in the `ReadOnlySafe` path. Found 2026-10-18 by the code review of the `raft-readindex-singleton-stale`
fix; the test written 2026-11-01. Upstream searched 2026-11-01 (`joint ReadIndex learner`): nothing.
