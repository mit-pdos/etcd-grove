---
upstream: none
checked: 2026-11-09
links:
  - nonissues/etcd-rangestream-negative-revision-unpinned.md: neighbouring
blocks-proof: no
---

# etcdserver: a streamed range at the current revision can fail with ErrCompacted before sending anything

`rangeStream` pins the revision of its pages at the first page's header revision
([`server/etcdserver/v3_server.go`](https://github.com/etcd-io/etcd/blob/main/server/etcdserver/v3_server.go),
`rangeStream`). When the first page already ends the stream (`!More || count == totalLimit`) with
`More` set, it counts the rest with `txn.Count(..., r.Revision)` at that pinned revision before
sending; if a write and a compaction past the pinned revision came between the two reads, the count
fails with `ErrCompacted` and the stream ends with "required revision has been compacted" and no
chunk, for a request that asked for the current revision.

**Why not an issue:** no test, found by code reading (2c's completeness review, round 1, F10); it needs
a compaction to the store's latest revision within the window of one request.

## Proof

no: the spec states it (`EtcdServer.RangeStream.spec`: a compaction error with any number of chunks
sent, no `Q`); 2a's `rsSink_out` and W0's stream contract must admit it with no chunk.

## Notes

A test could promote it: the `beforeRangeStreamChunk` failpoint does not fall between the first page
and the count; a failpoint before `txn.Count` would, with a put and a compaction at the store's
revision during the pause.
