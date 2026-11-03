---
upstream: none
checked: 2026-10-26
links:
  - etcd-io/etcd#17078 pr merged: introduced the `403` "cannot process message to mismatch member" in Process (2023, backported to 3.5 and 3.4) that the sender reads as errMemberRemoved
  - etcd-io/etcd#20356 issue closed: related (mismatch-member rejections in a 3.5.11 cluster that became unavailable; converted to a discussion without a root cause); no member reported stopping as removed
blocks-proof: no
---

# rafthttp: a message delivered to the wrong member makes the healthy sender stop as "removed"

If member A's pipeline for peer B posts to a URL served by another member C of the same cluster (a
stale peer URL after `UpdateMember`, a member re-created on a reused address), C's `Process`
answers `403` because the message is not addressed to it, the same status as for a removed
sender; A reads it as `errMemberRemoved` and stops with "data-dir used by this member must be
removed", although nobody removed it.

**Why not an issue:** no test; found by code reading (the code path is certain, the reachability of
a misaddressed peer URL is not shown). A test could promote it: an integration test that points one
member's peer URL for another at a third member's listener and checks that the sender stays up.

## Proof

no: the server's premise `transportEffectsOk` ("no well-behaved member reports `errMemberRemoved`
of a member never removed") holds when the peer URLs address the members they name, a deployment
premise a correctly configured etcd meets.

## Notes

Code: `EtcdServer.Process` (`server.go`, the `403` for `m.To` not the local member);
`pipelineHandler.ServeHTTP` (no `X-Raft-To` check, unlike the stream handler's `412`);
`checkPostResponse` (every `403` is `errMemberRemoved`); `pipeline.go`/`snapshot_sender.go`
(`reportCriticalError`); `run` stops on `errorc`. A fix: answer a misaddressed message with a
status the sender does not treat as fatal, or tell the two `403` bodies apart.
