---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# cache: after its upstream watch closes cleanly, the cache re-watches from the revision it first loaded

[`Cache.watch(rev)`](https://github.com/etcd-io/etcd/blob/a4d2bb1720b9/cache/cache.go#L340-L372)
loops: it registers a store watcher at `rev`, runs `watchEvents(rev, ...)`, and when the upstream
channel closes without an error (`watchEvents` returns `nil`) it goes round again with the **same**
`rev`, the revision after its initial list, although the demux and the store have since advanced.
The new upstream watch replays events the cache already applied; `demux.Broadcast` and
`store.Apply` reject them (`validateRevisions`: a stale or duplicate revision), `watchEvents` resets
readiness and returns the error, and the loop re-lists from scratch.

**Why not an issue:** no test; found by code reading (batch 1g's provability review). No wrong
answer: the replay is rejected and the cache re-lists; the cost is a readiness gap (`Watch` and
`Get` wait) and a full re-list after every clean close of the upstream channel (which the client
does when its context ends or its watcher closes, rare in practice). Liveness and efficiency only.

## Proof

no: liveness. The specs-only branch's `Cache.watchEvents.spec` and `demux.Broadcast.spec` admit the
rejected replay as an error arm.

## Notes

Fix, if wanted: continue from `demux.LatestRev() + 1` (or the store's latest revision `+ 1`) when
`watchEvents` returns `nil`.
