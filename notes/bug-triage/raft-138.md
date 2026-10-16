# etcd-io/raft#138: lagging follower commit after message drops

<https://github.com/etcd-io/raft/issues/138>. Open since 2024-01-25, label `enhancement`. No fix
merged: etcd-io/raft#139 ("advance commit index safely", the follower side) and #140 ("send
up-to-date commit index in heartbeats", the leader side) are open; #137 added the test that shows
the delay.

**The report.** `sendHeartbeat` (`raft.go:694` at the raft pin `509271dac`) sends `Commit =
min(pr.Match, committed)`. After a dropped `MsgAppResp`, the leader's `Match` for the follower
lags, so the follower learns that entries it already holds are committed only one round trip
later than it could (`HeartbeatInterval + 3/2 RTT` instead of `+ 1/2 RTT`). The cap exists because
the follower's `commitTo` panics on a commit index past its last index, and because the follower's
log is only known to agree with the leader's up to `Match`. The proposal moves the check to the
follower (#139: cut the commit index at the prefix known to match this leader's log, i.e. after a
successful `MsgApp` of this term) and then lifts the cap (#140), which needs every node upgraded
first (old followers would panic).

## Classification

**N** (an enhancement, not a bug), secondary **C-perf** (latency). The decisive fact: the pin has
the capped heartbeat, the behavior is the intended one, and the spec states it exactly — the
protocol model's `HeartbeatOk` (`Proof/go_etcd_io/raft/v3/Protocol/Model.lean:1525-1529`) requires
`m.commit ≤ s.commit ∧ m.commit ≤ matchOf s m.dst`, and `sendHeartbeat`'s proof meets it. The delay
is a latency property no spec here states.

## The code path and its verification state

Source: `/shared/etcd-grove-triage/coord/verified.txt`.

| Go function | State | Spec |
|---|---|---|
| `raft.sendHeartbeat` | verified | `Spec/go_etcd_io/raft/v3/raft__sendHeartbeat.lean` (`HeartbeatOk`) |
| `raft.handleHeartbeat` | verified | `Spec/go_etcd_io/raft/v3/raft__handleHeartbeat.lean` |
| `raftLog.commitTo` | verified | `Spec/go_etcd_io/raft/v3/raftLog__commitTo.lean` |
| `raft.maybeSendAppend` (`Commit` uncapped in `MsgApp`) | verified | `Spec/go_etcd_io/raft/v3/raft__maybeSendAppend.lean` (`AppOk`) |

## The argument (step 4), and what the proof says about the proposed change

1. *At the pin.* The follower's commit advances at a heartbeat by `plogCommitTo committed m.Commit`
   (`raft__handleHeartbeat.lean`, postcondition), and the panic in `commitTo` is excluded by the
   premise `m.Commit ≤ lastIndex`, which `raft.Step` discharges with the protocol fact
   `heartbeat_commit_le_last` (`Proof/go_etcd_io/raft/v3/Protocol/Facts.lean:66`): the leader sent
   `Commit ≤ pr.Match`, and `isMessage` carries the follower's own acknowledgement of `pr.Match` in
   that term, which is within its log. Nothing states *when* the follower's commit advances, so the
   one-RTT delay is admitted (C-perf: no latency statement, and none expressible as partial
   correctness).
2. *The proposed change (#140 alone).* Lifting the cap breaks `HeartbeatOk`'s second conjunct, and
   with it `heartbeat_commit_le_last`: the proof of `handleHeartbeat`'s premise fails exactly where
   the reported mixed-version crash is (an old follower's `commitTo` panic). So the proof would
   have caught the unsafe half of the fix on its own: an F+-style check of a proposed change.
3. *With #139.* The follower-side cut (commit only up to the prefix known to match the current
   leader) is what `stepFollower`'s `MsgApp` case already does for `MsgApp`'s uncapped `Commit`
   (`AppOk` has only `m.commit ≤ s.commit`; `raftLog.maybeAppend` commits `min(m.Commit, lastnewi)`, `log.go:129`).
   Verifying #139+#140 would replace `HeartbeatOk`'s `matchOf` conjunct by a follower-side
   invariant ("the log agrees with the term-`T` leader's up to `matchedIdx`", the ghost `leadPrefix`
   fact `handleAppendEntries` already has), a change the `etcd-pr-verify` skill could carry out
   when the PRs land.

## Proposal

None (class N). If #139/#140 merge: verify them with `.claude/skills/etcd-pr-verify`; the expected
spec change is item 3 above (medium: `HeartbeatOk`, `heartbeat_commit_le_last`, a new follower
field in `ownRaftPhys` and its ghost witness).

## Files

None besides this report.
