---
upstream: none
checked: 2026-11-14
links: []
blocks-proof: no
---

# etcdserver: a follower checks a lease call against its own auth state and lessor, and forwards it without the caller

With auth on, `LeaseTimeToLive` with keys and `LeaseKeepAlive` are checked on the member the client
talks to: its own auth store and its own lessor. A follower then forwards the call to the leader
over the peer port. The forwarded request carries only the lease ID (and the keys flag), and the
leader's lease handler checks nothing. `LeaseLeases` is answered from the local lessor alone. So a
follower that has not yet applied a permission change (a role revoked, a permission narrowed) still
lets the user read the keys of a lease, or keep it alive, under the old permissions. This is the
auth-state side of `etcd-lease-renew-keys-follower-lag.md` and of the follower case of
`../issues/etcd-lease-timetolive-keys-toctou.md`, which are about the lessor's side.

**Expected:** a lease call refused by the leader's current auth state should be refused through
every member, as the raft path is: a revocation or a leased put is re-checked at apply on every
member (`authApplierV3.LeaseRevoke`, `checkPutAuth`).

**Impact:** only with auth on, in the window after a permission change, through a follower that
lags. Key names (not values) of the lease leak, or a lease the user may no longer write is kept
alive. It is a permission race of the same kind as `etcd-compact-admin-check-lagging-member.md` and
`etcd-watch-lagging-member-auth-off.md`.

**Cause:** `LeaseTimeToLive` runs `checkLeaseTimeToLive` (`IsRangePermitted` on the local store,
of the keys of the local lessor's lease), then `leaseTimeToLive` forwards to the leader with
`leasehttp.TimeToLiveHTTP(cctx, id, r.Keys, lurl, s.peerRt)` (`server/etcdserver/v3_server.go:698-722,
636-696` at the etcd fork pin `2eaeb872bc`). `LeaseRenew` runs `checkLeaseRenew` locally, then
`leasehttp.RenewHTTP(cctx, id, lurl, s.peerRt)` (`:488-572`). The leader's `leaseHandler.ServeHTTP`
(`server/lease/leasehttp/http.go:58-170`) decodes the ID and answers from its lessor, with no auth
check.

**Why not an issue:** the auth-state lag is found by reading. The parts that are tested, at the pin
(`notes/auth-lease-scope/zz_authlease3_rows_test.go`): a follower refuses a user on its own check
before forwarding, root's call through a follower is answered from the leader's lessor, and leasehttp's own client calls (`TimeToLiveHTTP`, `RenewHTTP`), sent to the leader's peer URL
with no token, return the lease's keys and renew it. etcd treats the
peer port as trusted (peer TLS is the protection), and a follower's local checks are documented
behavior for the other local reads. A test of the lag itself would keep one member behind while its
peer HTTP still reaches the leader.

## Proof

no: `EtcdServer.LeaseTimeToLive.spec`, `LeaseRenew.spec` and `LeaseLeases.spec` state the check
over the receiving member's auth state and lessor, at the caller's lower bounds, which is what the
code does. A program that needs the leader's view makes each member apply past the change first
(the barrier of `notes/auth3-scope.md` §3).
