---
upstream: none
checked: 2026-10-21
links:
---

# A canceled watcher's responses taken after its canceled response stay buffered until the stream closes

- **Status**: bug, minor (memory held and never delivered; no wrong result). From code reading during
  the upstream report of [etcd-watch-id-reuse-stale-events](etcd-watch-id-reuse-stale-events.md);
  not reproduced on its own.
- **Where**: `server/etcdserver/api/v3rpc/watch.go` at upstream `main` b25719d10 (the same code as the
  pin `bc8b52a50`): `serverWatchStream.sendLoop`, the buffering of a response whose id is not
  announced (lines 470-476: `pending[wresp.WatchID] = append(...)`) and the cancel case (lines
  534-537: `delete(ids, wid)`, `pending[wid]` kept).
- **What happens**: `sendLoop` takes the mvcc watch stream's responses and the control responses in
  either order. When it takes a watcher's canceled response before that watcher's responses still
  queued in mvcc's channel, it removes the id from `ids`; each later response of the canceled watcher
  then finds its id not announced and is appended to `pending[id]`. Nothing deletes `pending[id]`
  unless a watch with the same id is created again (which flushes it to the new watch: the bug of
  `etcd-watch-id-reuse-stale-events`). So for a canceled id that is never reused, up to the channel's
  capacity (128 responses) per cancel stays in memory for the lifetime of the gRPC stream, never sent.
- **Expected**: a canceled watcher's responses are dropped ("No further events will be sent to the
  canceled watcher", `rpc.proto`), and their memory released.
- **How the proof handles it**: `sendLoop`'s proof models the buffering per watcher
  (`WatchSendModel.lean`); it promises nothing about memory, so nothing is assumed.
- **Possible fixes**: drop a canceled watcher's responses instead of buffering them; the upstream
  candidate for `etcd-watch-id-reuse-stale-events` (`issues/upstream/etcd-watch-id-reuse-stale-events/`)
  does so as part of its fix, on every stream (including those whose creates never wait: the drop
  needs no wait where ids are never reused); its PR does not mention this finding.
- **Found**: 2026-10-16, the upstream report of `etcd-watch-id-reuse-stale-events`.
