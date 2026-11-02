---
upstream: known
checked: 2026-11-01
links:
  - etcd-io/etcd#22673 issue open: filed by someone else 2026-10-30; its first consequence is this (pending grows for the stream's lifetime), its second is issues/etcd-watch-id-reuse-stale-events.md
  - etcd-io/etcd#22674 pr open: failing tests for #22673 (no fix)
blocks-proof: no
---

# watch: a canceled watch's queued responses stay buffered at the member until the stream closes

When the member's `sendLoop` takes a watch's canceled response before that watch's responses still
queued in mvcc's channel, it buffers them under the now unannounced ID and never releases them unless
the ID is reused: up to 128 responses per such cancel stay in memory, never sent, for the lifetime of
the gRPC stream.

**Why not an issue:** no test of ours (found by code reading while reporting
etcd-watch-id-reuse-stale-events); memory held, no wrong result, bounded per cancel (the user's
2026-10-23 review: non-issue).

## Proof

no: `sendLoop`'s proof models the buffering per watcher
(`Proof/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/WatchSendModel.lean`) and states nothing about
memory.

## Notes

Someone else has since filed it (#22673) with failing tests (#22674), counting it as unbounded growth
on a long-lived stream with many cancels (each cancel can leave up to 128 responses); worth a second
look. The fix branch of [etcd-watch-id-reuse-stale-events](../issues/etcd-watch-id-reuse-stale-events.md)
drops these responses on every stream, so it fixes this too.
