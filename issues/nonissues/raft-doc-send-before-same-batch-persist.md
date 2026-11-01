---
upstream: unchecked
checked: 2026-10-28
links: []
---

> Parked in `nonissues/` on filing (2026-10-28), as documentation findings are for now
> (`nonissues/README.md`). Found while planning the durability proof, not by a proof.

# raft: `doc.go` lets a follower send its acknowledgement before the entries it acknowledges are durable

- **Status**: documentation. The package documentation contradicts `Ready.Messages`' own
  documentation, and read literally, it permits an application to lose committed entries.
  It is not a bug in the code. Code reading only, with no reproduction.
- **Where**: etcd-raft at `509271dac` (the parent of the pinned `c8217eb9`, which changes only
  the probe-to-replicate shortcut):
  - `doc.go:79-86`, step 2 of handling a `Ready` (synchronous storage): "It is important that
    no messages be sent until the latest HardState has been persisted to disk, and all
    Entries written by any previous Ready batch (Messages may be sent while entries from the
    same batch are being persisted)." It then mentions the leader-only optimization of the
    Raft thesis §10.2.1.
  - `node.go:98-101`, `Ready.Messages`: "If async storage writes are not enabled, these
    messages must be sent AFTER Entries are appended to stable storage."
  - `rawnode.go:175-183` (`readyWithoutAccept`): with synchronous storage, `msgsAfterAppend` goes
    into `rd.Messages`. This includes a follower's `MsgAppResp` for the entries of the same
    `Ready`, and its `MsgVoteResp` granting a vote.
- **What happens**: `doc.go`'s parenthesis is not restricted to the leader. An application
  that follows it can send a follower's `MsgAppResp` for index `i` while entry `i` of the
  same batch is still being written. Suppose the follower then crashes before the write is
  durable. The leader may already have counted the acknowledgement toward a quorum and
  committed `i`. The follower restarts without the entry, so a quorum no longer holds it, and
  a later leader can be elected without it and overwrite it.

  The parenthesis is safe for the leader alone: the leader's own acknowledgement of its new
  entries is stepped at `Advance` (`stepsOnAdvance`), after the application persisted them.
  etcd's server follows `node.go`, not `doc.go`: `raftNode.start` sends before `Save` only when
  `rd.RaftState == StateLeader` (`server/etcdserver/raft.go:240-262` at the etcd pin).
- **Expected**: `doc.go` should say what `Ready.Messages` says. Only the leader may send its
  messages, which carry no acknowledgement of its own entries, while that batch's entries are
  being persisted. Every other message waits until the batch's `HardState` and `Entries` are
  durable.
- **How the proof handles it**: the current proof does not reach it, because it has no crash
  model (`notes/STATUS.md`, "Out of scope for now"). The durability plan
  (`notes/raft-durability-plan.md`, §4.2) makes every message of a `Ready` conditional on the
  batch being persisted, which is `node.go`'s contract. Its open question Q1 is whether a
  leader's `Ready` can carry a promise that is not yet durable.
- **Possible fixes**: reword the parenthesis to "(the leader may send its messages while the
  entries from the same batch are being persisted, see below)". Alternatively, drop it and
  keep only the §10.2.1 sentence, scoped to the leader.
- **Found**: 2026-10-28, reading raft's durability contract while planning the durability
  proof (`notes/raft-durability-plan.md`).
