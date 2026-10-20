---
upstream: none
checked: 2026-10-20
links:
  - etcd-io/raft#430 pr merged: related, flagged: a reviewer noted etcd mutates Ready.Messages (To = 0) and concluded there is no raft-side retained-pointer race; acceptReady's reads of handed-out messages were not considered
---

# raft v3.7: `node.go` reads `Ready.Messages` responses after handing the `Ready` out

- **Status**: open (not reported; not reproduced by a test). A documentation issue: an
  unstated precondition on the application.
- **Where**: raft v3.7 as pinned for `raft37` in `etc/goose.py` (fork commit `509271dac`):
  `rawnode.go:178-183` (`readyWithoutAccept` appends the `msgsAfterAppend` messages to other
  nodes to `rd.Messages`: the same `*pb.Message` pointers), `node.go:435-436` (`case readyc <-
  rd: n.rn.acceptReady(rd)`: the `Ready` is sent first), `rawnode.go:414-416` (`acceptReady`
  loops over `r.msgsAfterAppend` and calls `m.GetTo()` on every message, those handed out
  included). `Ready.Messages`' documentation (`node.go:98-110`) does not say the messages are
  read-only.
- **What happens**: once the application has received the `Ready` from `Node.Ready()`, `run`
  may still be reading the `To` field of each response (`MsgAppResp`, `MsgVoteResp`,
  `MsgPreVoteResp`) it handed out to another node. An application that writes such a message
  (e.g. clears `To` of a message to a removed member, as etcd did with value messages before
  v3.7) races with `run`. Before raft v3.7, messages were values: `rd.Messages` held copies,
  and nothing raft kept aliased them. etcd v3.7 only reads (`processMessages` skips a removed
  member's message), so etcd is not affected.
- **Expected**: either `Ready.Messages` documented as read-only until the next `Advance` (or
  at least the responses), or `acceptReady` not reading the handed-out messages (e.g. filtering
  `msgsAfterAppend` before the `Ready` is sent).
- **How the proof handles it**: `readyWithoutAccept` hands each response out at half
  (`readyDq`, `Raft37/Proof/go_etcd_io/raft/v3/InvRawnodeReady.lean`); the node keeps the other
  half (`ownRaftPhysReady`'s `Hother`) for `acceptReady`'s `GetTo`, so the application can only
  read them; every other message (a `MsgSnap`, which etcd rewrites) goes out whole.
- **Possible fixes**: document it; or in `acceptReady` remember the self-addressed messages
  found by `readyWithoutAccept` instead of re-reading `To`.
- **Found**: 2026-10-16, raft v3.7 retarget stage R5 phase 1 (the `Ready` predicates, D8).
