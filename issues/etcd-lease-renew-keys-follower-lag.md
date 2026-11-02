---
upstream: none
checked: 2026-11-02
links:
---

# server/etcdserver: a `LeaseRenew` forwarded from a follower checks the follower's stale key set

- **Status**: a candidate bug (an authorization gap), not yet reproduced. A non-admin user
  renews a lease through a lagging follower even though the lease holds a key the user may not
  write, which `checkLeaseRenew` exists to refuse. Found reading the code; same shape as
  [etcd-lease-timetolive-keys-toctou](etcd-lease-timetolive-keys-toctou.md)'s follower variant.
- **Where**: `server/etcdserver/v3_server.go` at 249d76bea (`etc/goose.py`'s etcd pin):
  - `EtcdServer.LeaseRenew` (`v3_server.go:488-571`): on the leader it waits for the applied
    index (`waitAppliedIndex`, `:511-522`), then runs `checkLeaseRenew` and `lessor.Renew`. On a
    follower it runs `checkLeaseRenew` (`:547`) and then forwards the renewal to the leader
    (`leasehttp.RenewHTTP`, `:551-557`), with no wait for any index.
  - `checkLeaseRenew` (`v3_server.go:574-605`): for a non-admin user it looks the lease up in the
    **local** lessor and requires `IsPutPermitted` on every key it holds then. A lease the local
    lessor does not have passes.
- **What happens** (expected; to be reproduced): user U may write `a` only, and lease L holds `a`.
  Root puts `b` with lease L. On a follower that has not yet applied that put, U's
  `KeepAlive(L)` passes the check on `{a}` and the leader renews L. U keeps `b` alive, which a
  renewal through the leader refuses (`etcdserver: permission denied`). The window is the
  follower's apply lag. On the leader a smaller window exists between the check and `Renew`.
  With `FastLeaseKeepAlive` (`v3_server.go:509-514`), the leader also skips `waitAppliedIndex`
  when the lease is found, so its own check reads a lessor that may lag its commit index: the
  same gap on the leader, for entries committed but not yet applied (found by the spec review,
  2026-11-01).
- **Expected**: the renewal is refused whenever the lease holds a key the user may not write, as
  on the leader after `waitAppliedIndex`.
- **How the proof handles it**: `EtcdServer.LeaseRenew.spec` (the lease-renew plan,
  `notes/lease-renew-plan.md`) states the check over the local lessor at a lower bound, nothing
  of the renewed lease; its margin names this gap.
- **Possible fixes**: on a follower, check on the leader (pass the principal through leasehttp
  and run the check in the leader's handler), or wait for the follower's applied index to reach
  the leader's commit index (a read index) before the check.
- **Found**: 2026-11-01, scoping the lease-renew plan (item 5 of the lessor/auth list).
