---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# etcdserver: a streamed range sends keys read after the user's read permission was revoked, then fails

`RangeStream` runs its whole paged read inside `doSerialize`'s `get`
([`server/etcdserver/v3_server.go`](https://github.com/etcd-io/etcd/blob/main/server/etcdserver/v3_server.go),
`RangeStream` and `rangeStream`): it checks the permission once, then reads and **sends** every page,
and only after the last `Send` does `doSerialize` compare the token's auth revision with the store's
and return `ErrAuthOldRevision`. If a `RoleRevokePermission` (or a `UserRevokeRole`, `UserDelete`)
applies between the check and the later pages, those pages, read after the revocation, have already
reached the client when the error comes. A unary `Range` drops its answer in the same situation
(nothing is sent before the re-check).

**Why not an issue:** no test, found by code reading (2c's specs, round 1); it needs a revocation
while a multi-page stream is being sent, and the client sees the error after the keys (a
well-behaved client discards them; the bytes were nonetheless delivered).

## Proof

no: the spec states it (`EtcdServer.RangeStream.spec`: a stale auth revision after every chunk was
sent, no `Q`; the caller's update's `Q` is given only with a `nil` return); W0's stream contract must
not let a client rely on chunks of a stream that ends in an error.

## Notes

Fix, if wanted: re-check the auth revision (when the request carried one) before each `Send`, and
end the stream with `ErrAuthOldRevision` before sending a page read after a change. A test could
promote it: a failpoint at `beforeRangeStreamChunk` (`rangeStream`), a stream of a user with read
permission over many keys, a `RoleRevokePermission` during the pause, and the client receiving the
next page before the error.
