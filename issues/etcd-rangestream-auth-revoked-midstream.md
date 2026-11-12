---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---
# etcdserver: a streamed range keeps sending keys after the user's read permission is revoked, then fails

With auth enabled, a `RangeStream` checks the user's read permission once, then reads and sends
every page; only after the last page does it notice that the auth store changed and end with
`ErrAuthOldRevision`. If the user's permission is revoked (`RoleRevokePermission`,
`UserRevokeRole`, `UserDelete`) while the stream runs, every page read after the revocation still
reaches the client before the error. A unary `Range` in the same situation returns only the error.

**Expected:** a user whose read permission has been revoked should receive no more keys of the
range, as a unary `Range` that observes the same revocation returns none.

**Impact:** clusters with auth enabled (not the default) and clients using `RangeStream` (etcd
v3.7+) over more than one page; a revocation that applies while the stream is being sent. The keys
sent are at the stream's pinned revision, which precedes the revocation; a client that discards a
stream ending in an error loses nothing, but the bytes reach it.

**Reproduction:** `TestV3AuthRangeStreamRevokedMidStream` in
[`issues/etcd-rangestream-auth-revoked-midstream/v3_auth_rangestream_revoke_test.go`](etcd-rangestream-auth-revoked-midstream/v3_auth_rangestream_revoke_test.go),
copied into `tests/integration` at etcd-io/etcd@d622ec57cf46 (2026-11-06), go1.27.3, with the
server's failpoints enabled (`make gofail-enable`; the test makes `beforeRangeStreamChunk` sleep 3s
before the second page, during which root revokes the permission and the revocation is seen to
apply):

```
$ go test ./integration -run '^TestV3AuthRangeStreamRevokedMidStream$' -count=1
--- FAIL: TestV3AuthRangeStreamRevokedMidStream (3.40s)
    v3_auth_rangestream_revoke_test.go:74: stream ended: rpc error: code = InvalidArgument desc = etcdserver: revision of auth store is old
        	Error:      	Should be zero, but was 90
        	Messages:   	keys sent to user1 after its read permission was revoked
FAIL
```

**Cause:** [`RangeStream`](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/server/etcdserver/v3_server.go#L158-L196)
runs the whole of [`rangeStream`](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/server/etcdserver/v3_server.go#L198-L274),
which reads and `Send`s every page, as `doSerialize`'s `get`;
[`doSerialize`](https://github.com/etcd-io/etcd/blob/d622ec57cf46c119f1a550343c34b26327cead0f/server/etcdserver/v3_server.go#L1036-L1058)
compares the token's auth revision with the store's only after `get` returns, which for a unary
request is before anything is sent.

## Proof

no: the spec states it (`EtcdServer.RangeStream.spec`: a stale auth revision after every chunk was
sent, no `Q`; the caller's update's `Q` is given only with a `nil` return); W0's stream contract must
not let a client rely on chunks of a stream that ends in an error.

## Fix

Not written: re-check the auth revision (when the request carried one) before each page's read,
and end the stream with `ErrAuthOldRevision` before sending a page read after a change.

## Notes

RBAC is a secondary control in etcd's threat model, and the keys are those the user could read at
the stream's revision: hardening, not a security report. Watches are checked only when created
(`v3rpc/watch.go`, `isWatchPermitted`), so a maintainer may see streams continuing past a revocation
as expected; the difference here is that the stream itself ends by declaring its reply stale.
