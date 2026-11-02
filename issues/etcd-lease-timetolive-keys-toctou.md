---
upstream: none
checked: 2026-11-02
links:
  - etcd-io/etcd#15656 pr merged: related, not this bug (GHSA-3p4g-rcw5-8298, CVE-2023-32082: added `checkLeaseTimeToLive`, the check this race gets past)
blocks-proof: no
---

# etcdserver: `LeaseTimeToLive` with `Keys` returns key names the caller may not read

With auth enabled, a user who may read some of a lease's keys calls `TimeToLive(lease,
WithAttachedKeys())` and gets back the names of keys attached to the lease after its permission
check, keys the user may not read (its `Get` of them is refused with permission denied). On the
leader the window is between the check and a second lookup of the lease; on a follower the check
reads the follower's own lessor and the keys come from the leader's, so any key attached to the
lease that the follower has not applied yet leaks, with no concurrency within the request.

**Expected:** `LeaseTimeToLive` with `Keys` should return a key only to a user who may read it, as
its permission check intends ("check RBAC permission only if Keys is true",
[`v3_server.go#L707`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/v3_server.go#L707)),
added for GHSA-3p4g-rcw5-8298 (etcd-io/etcd#15656).

**Impact:** clusters with auth enabled, where a non-admin user may read some but not all keys
attached to a lease, and another user (or root) attaches keys to that lease. The names of the keys
leak, not their values. On the leader it is a race; on a follower the window is the follower's
apply lag.

**Reproduction:** `TestV3LeaseTimeToLiveKeysTOCTOU` in
[`issues/etcd-lease-timetolive-keys-toctou/v3_lease_ttl_keys_toctou_test.go`](etcd-lease-timetolive-keys-toctou/v3_lease_ttl_keys_toctou_test.go),
copied into `tests/integration` at etcd-io/etcd@a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5
(2026-11-02), go1.27.3 linux/amd64, with gofail enabled in `server/etcdserver` and
`server/lease/leasehttp` (`gofail enable server/etcdserver/ server/lease/leasehttp/`). The leader
case (one member) sleeps at the existing failpoint `beforeLookupWhenLeaseTimeToLive`, between the
check and the second lookup; the follower case (three members, the user's client on a follower)
at `beforeLookupWhenForwardLeaseTimeToLive` in the leader's lease handler. The failpoints only
widen the window; not measured without gofail.

```
$ go test ./integration/ -run '^TestV3LeaseTimeToLiveKeysTOCTOU$' -count=1 -v
    v3_lease_ttl_keys_toctou_test.go:122: keys returned to u: [a b]
        	Error:      	[]string{"a", "b"} should not contain "b"
        	Test:       	TestV3LeaseTimeToLiveKeysTOCTOU/leader
        	Messages:   	LeaseTimeToLive returned a key the caller may not read
    v3_lease_ttl_keys_toctou_test.go:122: keys returned to u: [a b]
        	Error:      	[]string{"a", "b"} should not contain "b"
        	Test:       	TestV3LeaseTimeToLiveKeysTOCTOU/follower
        	Messages:   	LeaseTimeToLive returned a key the caller may not read
--- FAIL: TestV3LeaseTimeToLiveKeysTOCTOU (5.11s)
    --- FAIL: TestV3LeaseTimeToLiveKeysTOCTOU/leader (2.39s)
    --- FAIL: TestV3LeaseTimeToLiveKeysTOCTOU/follower (2.71s)
FAIL	go.etcd.io/etcd/tests/v3/integration	5.279s
```

**Cause:** [`LeaseTimeToLive`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/v3_server.go#L699-L725)
runs [`checkLeaseTimeToLive`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/v3_server.go#L608-L634),
which requires `IsRangePermitted` on the keys the **local** lessor holds for the lease, then
[`leaseTimeToLive`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/v3_server.go#L637-L697),
which looks the lease up again (on the leader after `waitAppliedIndex`,
[L646-L658](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/v3_server.go#L646-L658);
on a follower in the leader's lessor, through the lease handler) and returns the keys it holds
then. Afterwards only the auth store's revision is re-checked
([L720](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/v3_server.go#L720)),
which a put does not change. A put with a lease requires write permission on the key and on the
keys the lease already holds
([`checkLeasePuts`](https://github.com/etcd-io/etcd/blob/a2e3642bcd2cca3a802503cdb09f64a3dc15cdf5/server/etcdserver/apply/auth.go#L198-L220)),
nothing about who may read the lease's keys.

## Proof

no: the top-level adequacy proof needs no fix on the goosed fork for it; `EtcdServer.LeaseTimeToLive.spec`
(`Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__LeaseTimeToLive.lean`) states the
permission check over the keys it checked, not the keys it returns (its margin); the intended
guarantee, a key returned only to a user who may read it, is false here.

## Fix

Not written. Check permission on the keys actually returned, after the lookup that produces them:
in `LeaseTimeToLive`, after `leaseTimeToLive` returns, run `IsRangePermitted` on each of
`resp.Keys` (keeping the revision re-check), which covers the leader and the follower paths alike.
Filtering `resp.Keys` to the readable ones is the alternative, though refusing matches the current
semantics (the whole request fails if any key is unreadable).

## Notes

Not a security report (checked against etcd's `THREAT_MODEL.md`, 2026-11-02): RBAC is "an optional, secondary control" there, off by default, and "name-enumeration leaks behind the transport boundary are hardening concerns, not vulnerabilities"; it leaks key names (not values) to an authenticated user, only with auth enabled. File it as a normal issue.

The same shape for `LeaseRenew`'s write check is
`nonissues/etcd-lease-renew-keys-follower-lag.md`.
