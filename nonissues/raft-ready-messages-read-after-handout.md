---
upstream: none
checked: 2026-10-21
links:
  - etcd-io/raft#430 pr merged: related, flagged: a reviewer noted etcd mutates Ready.Messages (To = 0) and concluded there is no raft-side retained-pointer race; acceptReady's reads of handed-out messages were not considered
blocks-proof: no
---
# raft v3.7: `node.run` reads `Ready.Messages` responses after handing the `Ready` out

In raft v3.7 messages are pointers, and `node.run` sends a `Ready` to the application and then
calls `acceptReady`, which reads `To` of every response (`MsgAppResp`, `MsgVoteResp`,
`MsgPreVoteResp`) it has just handed out in `Ready.Messages`. An application that writes such a
message (as etcd did with value messages before v3.7, clearing `To` of a message to a removed
member) races with `run`. `Ready.Messages`' documentation does not say the messages are read-only.

**Why not an issue:** no test (code reading); a precondition etcd meets (v3.7's
`processMessages` only reads the messages); at most worth documenting (INDEX-reviewed.md's Plan:
"Nonissue; maybe some docs").

## Proof

no: `readyWithoutAccept` hands each response out at half (`readyDq`,
`Spec/go_etcd_io/raft/v3/RawNode__readyWithoutAccept.lean`), keeping the other half for
`acceptReady`, so the application may only read it, as etcd does.

## Notes

A race test with an application writing `To` (under `-race`) could show the race, but would still
use the messages in a way etcd does not. A fix would have `acceptReady` remember the
self-addressed messages instead of re-reading `To`.
