---
upstream: none
checked: 2026-11-02
links: []
blocks-proof: yes
---

# etcdserver: a `LeaseRenew` through a lagging follower checks the follower's stale key set

With auth enabled, `checkLeaseRenew` refuses a non-admin user's renewal of a lease holding a key the
user may not write. On a follower it reads the follower's **local** lessor and then forwards the
renewal to the leader with no wait for any index
([`LeaseRenew`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/v3_server.go#L538-L561),
[`checkLeaseRenew`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/v3_server.go#L575-L606)),
so a user U who may write `a` only keeps alive a lease that root attached `b` to, while the follower
has not applied that put; a lease the local lessor does not have passes. On the leader with
`FastLeaseKeepAlive` and the lease found, `waitAppliedIndex` is skipped
([L512-L518](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/v3_server.go#L512-L518)),
the same gap for entries committed but not yet applied; and on the leader a smaller window lies
between the check and `Renew`'s own lookup.

**Why not an issue:** no test; found by code reading (scoping the lease-renew plan,
`notes/lease-renew-plan.md`). A test could promote it, as `issues/etcd-lease-timetolive-keys-toctou.md`'s
follower case did for `TimeToLive`: a three-member integration cluster, U's client on a follower
that has not yet applied root's `Put("b", WithLease(L))`, and U's `KeepAliveOnce(L)` succeeding
where the leader refuses it with permission denied (keeping one member behind is the work: gofail
failpoints are process-wide in the integration framework).

## Proof

yes: `EtcdServer.LeaseRenew.spec` (`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__LeaseRenew.lean`)
states the check over the local lessor at a lower bound, nothing of the renewed lease (its margin
names this gap); the intended guarantee, no renewal of a lease holding a key the user may not
write, would be false here.

## Notes

Fix, if wanted: on a follower, run the check on the leader (pass the principal through leasehttp and
check in the leader's handler), or wait for the follower's applied index to reach the leader's
commit index (a read index) before the check. If a test confirms it, it crosses a permission line,
like `etcd-lease-timetolive-keys-toctou` (on hold for the private security process).
