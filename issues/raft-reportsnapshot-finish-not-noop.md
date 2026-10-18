---
upstream: unchecked
checked: 2026-10-18
links:
---

# raft: `Node.ReportSnapshot`'s comment says `SnapshotFinish` is a no-op; without it a leader can stay paused on a follower forever

- **Status**: documentation the code contradicts (and the other raft docs). Reproduced by a temporary Go test
  (below); found while revising the `raft-snapshot-during-apply-stale-confchange` candidate, whose first fix
  depended on `ReportSnapshot` (2026-10-18).
- **Where** (etcd-io/raft `main` 638f42739):
  - `node.go:230-240`, `Node.ReportSnapshot`: "Calling ReportSnapshot with SnapshotFinish is a no-op. But, any
    failure ... should be reported to the leader with SnapshotFailure."
  - `raft.go:1611-1628` (`stepLeader`, `MsgSnapStatus`): for a progress in `StateSnapshot`, `SnapshotFinish` moves
    it to `StateProbe` (from the snapshot's index), and the leader probes the follower again after its next
    heartbeat response. Not a no-op.
  - `raft.go:1579-1598` (`MsgHeartbeatResp`): a progress in `StateSnapshot` is paused, so heartbeat responses send
    nothing; the only other way out of `StateSnapshot` is the follower's `MsgAppResp` reaching the leader's first
    index (`raft.go:1531`).
  - `doc.go:85` ("If any Message has type MsgSnap, call Node.ReportSnapshot() after it has been sent") and
    `node.go:108-109` (`Ready.Messages`: "the application MUST report back to raft when the snapshot has been
    received or has failed") require the call, which contradicts "no-op".
- **What happens**: the follower restores the leader's snapshot, and its answer (`MsgAppResp` at the snapshot's
  index) is lost; raft allows any message to be lost. An application that trusts the comment and reports only
  failures never calls `ReportSnapshot(SnapshotFinish)`: the leader's progress of that follower stays in
  `StateSnapshot`, paused, until the leader changes. In a two-voter cluster the leader cannot commit at all.
  A temporary test (2026-10-18, `go test -overlay` adding a file to package `raft` at 638f42739): leader 1 of
  `{1,2}` with its log compacted at index 10 (`newTestRaft`, `becomeCandidate`/`becomeLeader`), follower 2 empty;
  messages pumped by hand, dropping only the follower's first non-reject `MsgAppResp` at index ≥ 10; 20
  heartbeat rounds and a proposal:

      report=false: snapshots sent 1; after 20 heartbeats and a proposal: leader last 12 commit 10; follower last 10 commit 10; leader's progress StateSnapshot match=0 next=11 paused pendingSnap=10
      report=true: snapshots sent 1; after 20 heartbeats and a proposal: leader last 12 commit 12; follower last 12 commit 12; leader's progress StateReplicate match=12 next=13

  (`report=true` steps `MsgSnapStatus` without reject, what `ReportSnapshot(id, SnapshotFinish)` sends, after the
  first round.) etcd calls `ReportSnapshot(SnapshotFinish)` after each upload, so etcd is not affected.
- **Expected**: the comment says that `SnapshotFinish` must be reported too (it resumes probing of the follower;
  without it, a lost answer to the snapshot leaves the leader paused on that follower), consistent with `doc.go`
  and `Ready.Messages`.
- **How the proof handles it**: not reached; the verified scope does not model snapshot transfer or
  `ReportSnapshot`.
- **Possible fixes**: fix the comment ("Calling ReportSnapshot with SnapshotFinish is a no-op" → the leader
  resumes probing the follower from the snapshot's index); or make a heartbeat response of a follower in
  `StateSnapshot` probe it after a while (a behavior change).
- **Found**: 2026-10-18, revising the fix of `raft-snapshot-during-apply-stale-confchange` (whose first fix made the
  leader's resend depend on `ReportSnapshot`); reproduced by the temporary test above.
