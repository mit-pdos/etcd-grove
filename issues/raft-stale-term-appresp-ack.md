---
upstream: unchecked
---
# raft: the reply to a stale-term `MsgApp` reads as an acceptance of index 0 and resets `Next` to 1

**Status**: a bug, of efficiency rather than safety in the pinned code: the leader
resends its whole log, or a snapshot, to a follower that already has it. With
etcd-io/raft#140 applied it becomes a safety bug (below).

**Where**: raft v3.7 as pinned (`raft37-goose-lean`, `509271dac`):
- `raft.go:1134-1157`, `Step`, `m.Term < r.Term`: with `checkQuorum` or `preVote` on, a
  `MsgApp`/`MsgHeartbeat` of an older term is answered with
  `r.send(&pb.Message{To: m.From, Type: pb.MsgAppResp.Enum()})`. The comment says the reply
  is there so that a deposed leader sees the higher term and steps down. `send` stamps it
  with `r.Term`. It carries `Index: 0` and `Reject: false`.
- `raft.go:1519`, `stepLeader`, `MsgAppResp`:
  `if pr.MaybeUpdate(m.GetIndex()) || (pr.Match == m.GetIndex() && pr.State == tracker.StateProbe)`
  then `pr.BecomeReplicate()` (`tracker/progress.go`: `Next = Match + 1`).

**What happens**: the sender of the old `MsgApp` may since have become the leader of the
follower's current term, for example node 2 at term 2, and again at term 4. The reply then
arrives at the term it was meant for. The leader takes it for an acceptance of index 0. While
it is still probing the follower (`StateProbe`, `Match = 0`), it moves to `StateReplicate` with
`Next = 1`. It then sends the log from index 1, or a snapshot when the log is compacted,
although the follower may hold all of it.

Reproduction: `TestStaleTermAppRespRegressesNext`, in
`notes/pr-verify/raft-140-tests/fork-v3.7/staleack_repro_test.go`. Copy it into the pinned raft checkout
and run `go test -run TestStaleTermAppRespRegressesNext .`. It fails with
`Progress[3] = StateReplicate match=0 next=5 inflight=1`: the leader sent entries 1..4.

**Expected**: the step-down nudge is not an acknowledgement. It should be recognisable as
such, for instance by `Reject: true` with a hint, or by a field the leader ignores, and should
not move a probing `Progress`.

**How the proof handles it**: as harmless. `isMessage` of an accepting `appResp` carries
`isAcked src term index`, and an acknowledgement of index 0 holds trivially (`isAcked`'s
`uint.Z i = 0` case, `Protocol/Ghost.lean`). The leader's `Match` does not move. Its `Next` is
not part of the protocol state.

**Why it matters with etcd-io/raft#140**: the regressed `Next` makes the leader send `MsgApp`s
that end below the follower's divergence point, cut by `MaxSizePerMsg`. The follower accepts
one without a conflict, keeps an older-term tail, and sets `logSynced`. A heartbeat carrying
the leader's commit index then commits that stale tail. See
`notes/pr-verify/raft-140.md`, `TestLogSyncedBogusAckStaleTail`.

**Possible fixes**: answer with `Reject: true` (and a `RejectHint` of the follower's last
index), which `MaybeDecrTo` ignores outside the current probe. Or have `stepLeader` ignore a
`MsgAppResp` with `Index == 0`, whose acceptance carries no information.

**Found**: 2026-10-16, by the review of the etcd-io/raft#140 verification, searching for a
schedule that breaks the PR's `logSynced` claim.
