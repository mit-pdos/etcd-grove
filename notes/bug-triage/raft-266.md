# etcd-io/raft#266: leader election not triggered under simplex leader partitions

<https://github.com/etcd-io/raft/issues/266>. Filed 2025-02-14, closed 2025-02-17 by the reporter,
with no comment, label, PR or commit. No version given; the reporter ran a 9-member etcd cluster.

**The report.** An attack script makes every link *into* the leader lossy ("high loss") for 2 s,
then restores it for 3 s, repeatedly. The leader keeps sending `MsgApp`/`MsgHeartbeat`, so no
follower's election timer fires (`stepFollower` resets `electionElapsed` on every message from the
leader), and the leader is never replaced, although it hears few or no acknowledgements and the
cluster makes little progress. The proposed fix: followers should also time out when nothing is
committed for a long time.

## Classification

**N** (not a bug: the behavior is Raft's design, and the request is a new failure detector),
secondary **C-live**. The decisive facts: in Raft a follower's only failure detector is the
leader's traffic, and a leader that cannot hear its quorum is removed by `CheckQuorum`
(`stepLeader`'s `MsgCheckQuorum` case, `raft.go:1281-1285`), which etcd enables
(`server/etcdserver/bootstrap.go:572`, `CheckQuorum: true`) and which steps the leader down after
an election timeout with no message from a quorum — under *total* loss of the incoming links. Under
*partial* loss some responses arrive, `QuorumActive()` stays true, and the leader stays: an
availability (liveness) question, which no spec here states. The specs are partial correctness and
leave every progress question open, so nothing excludes the report, and nothing in it contradicts
safety (one leader per term, committed prefixes agree).

## The code path and its verification state

Source: `/shared/etcd-grove-triage/coord/verified.txt` (raft pin `509271dac`).

| Go function | State | Spec |
|---|---|---|
| `raft.tickElection` | verified | `Spec/go_etcd_io/raft/v3/raft__tickElection.lean` |
| `raft.tickHeartbeat` (emits `MsgCheckQuorum`) | verified | `Spec/go_etcd_io/raft/v3/raft__tickHeartbeat.lean` |
| `stepFollower` (`MsgApp`/`MsgHeartbeat`: `electionElapsed = 0`) | verified | `Spec/go_etcd_io/raft/v3/stepFollower.lean` |
| `stepLeader`, `MsgCheckQuorum` case | verified, but only with `CheckQuorum = false` | `Spec/go_etcd_io/raft/v3/stepLeader.lean` |

## The argument (step 4)

1. *As the spec sees it*: a trace where one node leads term `T` forever, every other node stays a
   follower of `T`, and the commit index stops (or crawls). Every step of it is a `Step` of the
   protocol model; no safety result (`Proof/go_etcd_io/raft/v3/Results.lean`) says anything
   about it, because nothing bad happens — no second leader, no divergent commit.
2. *Premises.* Every raft entry point the proof covers takes `cv.CheckQuorum' = false`
   (`Spec/go_etcd_io/raft/v3/newRaft.lean:128`, `NewRawNode.lean:106`, `StartNode.lean:75`,
   `RestartNode.lean:54`; `ownRaftPhys`'s `HnoCheckQuorum`,
   `Proof/go_etcd_io/raft/v3/InvRaftPhys.lean:813`), while etcd runs with `CheckQuorum: true`. So
   the one mechanism that bears on this report is outside the verified configuration. That is a
   known, deliberate scope choice (`notes/decisions.md`, "etcd's `CheckQuorum` and `PreVote`
   settings stay premises"), and it is not what lets this report through: with `CheckQuorum` on,
   the reported behavior (partial loss, leader kept) is still what the code is meant to do.
3. *Postconditions.* Partial correctness: `tickElection`'s spec says the node campaigns once past
   the randomized timeout and otherwise only increments `electionElapsed`; `stepFollower`'s says a
   message from the leader resets it. A trace in which the timeout is never reached meets both. What
   the reporter expected ("a new leader within some bound when commits stop") is a liveness
   property under a fault model (a partially lossy network), which Iris-style specs do not express.

## Proposal

None (class N). Two remarks for the index:

- The nearest safety statement, if `CheckQuorum` is ever brought into scope: `stepLeader`'s
  `MsgCheckQuorum` case returns a follower whenever fewer than a quorum of voters have
  `RecentActive`, and `RecentActive` is set only by a message received from that voter since the
  previous check. It would document `CheckQuorum`'s step-down rule exactly, but would not change
  this report's outcome (partial loss keeps `RecentActive` true).
- The reporter's proposed fix (followers time out on a stalled commit index) would be a protocol
  change; its safety would be re-proved through `tickElection`'s spec (a new campaign trigger is
  safe for leader uniqueness, which rests on votes, not on why a node campaigns).

## Files

None besides this report.
