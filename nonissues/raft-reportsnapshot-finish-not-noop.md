---
upstream: known
checked: 2026-11-01
links:
  - etcd-io/raft#243 pr open: fixes this comment ("Fixes incorrect documentation that claimed SnapshotFinish was a no-op"), inside a breaking v4 change (`ReportSnapshot` takes the applied index, `PendingSnapshot` removed); no review, needs rebase
  - etcd-io/raft#124 issue open: related, not this bug: the snapshot-handling cleanup #243 implements
blocks-proof: no
---
# raft: `Node.ReportSnapshot`'s comment says `SnapshotFinish` is a no-op; without it a leader can stay paused on a follower

`Node.ReportSnapshot` says "Calling ReportSnapshot with SnapshotFinish is a no-op", but it moves
the follower's progress out of `StateSnapshot` (`stepLeader`, `MsgSnapStatus`). An application that
trusts the comment and reports only failures leaves the leader paused on that follower forever if
the follower's answer to the snapshot is lost (heartbeat responses send nothing to a paused
progress); in a two-voter cluster the leader then cannot commit.

**Why not an issue:** documentation only, contradicted by the other raft docs (doc.go: "call
Node.ReportSnapshot() after it has been sent"; `Ready.Messages`: "MUST report back to raft when
the snapshot has been received or has failed"); etcd always reports `SnapshotFinish` after an
upload, and the comment's fix is in etcd-io/raft#243.

## Proof

no: the verified scope does not model snapshot transfer or `ReportSnapshot`.

## Notes

Reproduced 2026-10-18 by a temporary test (not kept): leader 1 of `{1,2}` with its log compacted,
the follower's first `MsgAppResp` after the snapshot dropped; without the report the leader stays
at commit 10 with the progress `StateSnapshot ... paused` after 20 heartbeats and a proposal, with
it both reach 12. INDEX-reviewed.md's Plan: "Wait to see if it gets merged" (#243).
