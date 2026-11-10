---
upstream: none
checked: 2026-11-10
links:
  - etcd-io/etcd#17078 pr merged: introduced the `403` "cannot process message to mismatch member" in Process (2023, backported to 3.5 and 3.4) that the sender would read as errMemberRemoved
  - etcd-io/etcd#20356 issue closed: related (mismatch-member rejections in a 3.5.11 cluster that became unavailable; converted to a discussion without a root cause); no member reported stopping as removed
blocks-proof: no
---

# rafthttp: a message delivered to the wrong member would make the healthy sender stop as "removed" (latent)

If member A's pipeline for peer B posts to a URL served by another member C of the same cluster (a
stale peer URL after `UpdateMember`, a member re-created on a reused address), C's `Process`
rejects it with a `403`, the same status as for a removed sender, which A's `checkPostResponse`
reads as `errMemberRemoved` and stops on. Today the `403` never reaches A: C's handler answers
`500` and panics instead (`issues/etcd-rafthttp-pipeline-process-error-panic.md`), and A treats a
`500` as transient. The bug appears once that issue is fixed by letting the `403` through.

**Why not an issue:** unreachable at upstream `main` (etcd-io/etcd@fc81ffd2) and the pinned fork
(upamanyus/etcd@a4d2bb17); latent behind the pipeline-panic issue, whose fix must avoid it.
Checked on every path a misaddressed message takes: the pipeline (`/raft`) and snapshot
(`/raft/snapshot`) handlers never write `403` (their `writerToResponse` branch is dead: both answer
`500`); the stream handler answers a mismatched `X-Raft-To` with
[`412`](https://github.com/etcd-io/etcd/blob/fc81ffd2d5d79d4c685e476cedb7c5296ee019c4/server/etcdserver/api/rafthttp/http.go#L435-L448), which the stream reader treats as
transient, and answers [`410`](https://github.com/etcd-io/etcd/blob/fc81ffd2d5d79d4c685e476cedb7c5296ee019c4/server/etcdserver/api/rafthttp/http.go#L405-L414), the one
status it treats as removal, only when the dialing member itself is removed. Confirmed by the
crashreconf test (`notes/specs-only/crashreconf-test.md`, "Findings" 2): misaddressed messages
through a reused peer URL get `500` (the nodes' `out.log` show the recovered panic).

## Proof

no: no healthy member reports `errMemberRemoved` at the pinned code, whatever its peer URLs
address, so the server's premise `transportEffectsOk` ("no well-behaved member reports
`errMemberRemoved` of a member never removed") holds without assuming that the peer URLs address
the members they name (a reused peer URL, as in the crashreconf test, is fine). It would block the
proof if the fork took the panic fix without the `412` change of its `fix.patch`.

## Notes

Code: `EtcdServer.Process` (`server.go`, the `403` for `m.To` not the local member);
`pipelineHandler.ServeHTTP` (no `X-Raft-To` check, unlike the stream handler's `412`);
`checkPostResponse` (every `403` is `errMemberRemoved`); `pipeline.go`/`snapshot_sender.go`
(`reportCriticalError`); `run` stops on `errorc`. The fix (in the issue's `fix.patch`): answer a
misaddressed message with a status the sender does not treat as fatal (`412`), or tell the two
`403` bodies apart.
