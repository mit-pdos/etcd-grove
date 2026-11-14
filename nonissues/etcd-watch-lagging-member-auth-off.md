---
upstream: none
checked: 2026-11-14
links:
  - etcd-io/etcd#18437 issue closed: related, not this behavior (a simple token used at a member that has not applied its Authenticate entry is refused; documented as a known issue of simple tokens)
  - etcd-io/etcd#18487 issue closed: related, not this behavior (the auth admin reads go through raft instead of a read index)
blocks-proof: no
---

# etcdserver: after AuthEnable returns, a member that has not applied it yet still creates watches with auth off

In a cluster, once `AuthEnable` has returned to the administrator, a member that is behind (it has
not applied the `AuthEnable` entry yet: a slow or briefly cut-off follower) still accepts an
unauthenticated client's watch of any key and streams its events, including events from revision 1
that the client may not read once auth is on. A serializable read there is answered with auth off
too. The watch stays open after the member applies `AuthEnable`.

**Why not an issue:** not a guarantee etcd makes: watch creation and serializable reads are served
from the member's own applied state, auth state included, with no read index (the documented
staleness of serializable reads; nothing documents that `AuthEnable` takes effect on every member
when it returns). The linearizable paths wait for the member to apply past `AuthEnable`:
`Authenticate` (`server/etcdserver/v3_server.go:838`) and a linearizable `Range`
(`v3_server.go:138-144`) call `LinearizableReadNotify` before checking, and writes are checked at
apply, after `AuthEnable` in the log, on every member.

## Proof

no: `etcd_auth_safe` has one member, which has applied `AuthEnable` before `SetUp` returns (the
request waits for its own apply). A three-member variant whose principals' watches can reach a
follower must first make every member apply past `AuthEnable`, for example with a linearizable read
through each member after `SetUp` (`notes/auth3-scope.md`, section 3).

## Notes

The test,
[`nonissues/etcd-watch-lagging-member-auth-off/lagging_member_watch_test.go`](etcd-watch-lagging-member-auth-off/lagging_member_watch_test.go)
(`tests/integration`), passes at the etcd fork pin `2eaeb872b` (go1.27.1, 3 of 3 runs): a 3-member
cluster, a put of `secret`, a follower cut off (`InjectPartition`, etcd's `CutPeer`), root set up and
auth enabled through the leader; then through the follower an anonymous watch of `secret` from
revision 1 reports the put, and a serializable `Get` returns it, while an anonymous `Get` through
the leader is refused and `Authenticate` through the follower times out (it waits for a read
index) instead of answering `ErrAuthNotEnabled`. Found by code reading
(`server/etcdserver/api/v3rpc/watch.go:239-248`, `isWatchPermitted`, checks the member's own auth
store with no read index) while scoping the three-member auth example. Upstream searched 2026-11-14
(GitHub search: watch, auth enable, follower, serializable, linearizable): nothing on this behavior.
