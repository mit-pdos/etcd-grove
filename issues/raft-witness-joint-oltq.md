---
upstream: unchecked
---

# A joint configuration's witness is written on one half's acknowledgements only

**Status**: a bug (Leader Completeness, so State Machine Safety): raft#168's witness, as rebased on
the fork's `raft-witness-goose-lean` (through commit `9ed005d46`). **Fixed in the fork**, commit
`99cb9e2d9` (test `TestWitnessJointOutgoingOnlyReplication`); row 15 of
`notes/raft-witness-vs-pr168.md`.

**Where**: `tracker/tracker.go`, `ProgressTracker.OneLessThanQuorumInReplicationSet` (called by
`raft.maybeCommit`, whose `sendAppendToWitness` sends the witness the entry and both halves'
replication sets, `ReplicationSet[0]` stored by the witness as the set it checks votes against,
`witness.go`'s `handleAppend`/`handleVote`); `ChangeReplicationSet`, which excludes a voter per half
(the first inactive one in map iteration order).

**What happens**: in a joint configuration whose halves share the witness (`EnterJoint` copies
`Witnesses[0]` to `Witnesses[1]`), the witness's acknowledgement counts toward the commit of both
halves (`Committed` reads every voter's `Match`), but `OneLessThanQuorumInReplicationSet` reports the
witness as soon as one half has it in its replication set, at that half's quorum−1 index. When the
other half excludes the witness, the witness stores (`ReplicationSet[0]`, the incoming half's
non-witness voters) a set that no acknowledgement backs, and grants a vote to a candidate whose
responders lie in it. With both halves of odd size this elects a leader without a committed entry:

1. `(1 2 W)`, then one `ConfChangeV2` adding 3 and 4 (`(1 2 3 4 W) && (1 2 W)`, `W = 5`).
2. Leader 1's replication sets come to exclude `W` in the incoming half and 2 in the outgoing
   half (with 2 and 3 inactive the halves exclude 3 and 2; then, 3 back and `W` inactive, the
   incoming half replaces 3 by `W` and the outgoing half keeps 2).
3. An entry `e` acknowledged by 1 alone (quorum−1 of the outgoing set `{1}`) is sent to `W`,
   which stores `(term, subterm)` with the incoming set `{1, 2, 3, 4}`; with 4's acknowledgement
   `e` commits (incoming `{1, 4, W}`, outgoing `{1, W}`).
4. Node 2, whose log ends in the same subterm without `e`, campaigns: 3 votes for it, so it is one
   vote short in both halves and asks `W`; the responders `{2, 3}` are in the stored set and its
   last `(term, subterm)` is `W`'s, so `W` grants. Node 2 wins without `e`.

Reproduction: `TestWitnessJointOutgoingOnlyReplication` (`witness_joint_test.go` in the fork; it
fails at `9ed005d46`: "node 2 elected in term 2 without the entry 5 (term 1) node 1 committed"), and
the model checker's directed trace `issues/raft-witness-reconfig-model/traces/joint-oltq.txt`
(`runs/t1-joint-oltq-replay.txt`: leader completeness violated). The model's earlier runs missed
it: their joint changes applied one change, so one half was always of even size, where the
acknowledgements and the votes must meet.

**Expected**: a witness acknowledgement implies quorum−1 acknowledgements of the replication set
of every half the witness is a voter of (the static argument's `H`), so that its votes are
justified in the incoming half.

**How the proof handles it**: the static-mode proof (W2) has one configuration, where the case
cannot arise. The dynamic-mode proof (W5) is written for the fixed code; W3a's
`OneLessThanQuorumInReplicationSet` spec (`OltqOk`) gains the condition that a witness of both
halves is reported only when both halves have it in their replication sets.

**Possible fixes**: the fork's: report the witness of both halves only when both halves'
replication sets include it (at the minimum of the two indices, as before). Alternatively, have
the witness check the responders in the outgoing half against the stored outgoing set too (the
model's `rsout`); the first keeps the static argument's shape.

**Found**: 2026-10-20, designing the dynamic-mode (reconfiguration) proof of the witness (W5).
