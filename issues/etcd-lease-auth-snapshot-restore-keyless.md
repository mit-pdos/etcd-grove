---
upstream: none
checked: 2026-11-27
links:
  - etcd-io/etcd#15656 pr merged: related, not this bug (GHSA-3p4g-rcw5-8298, CVE-2023-32082: added `checkLeaseTimeToLive`, one of the two checks the restore window gets past)
blocks-proof: yes
---

# etcdserver: while a member restores a snapshot, `LeaseLeases` and `LeaseTimeToLive` with keys skip the lease-key permission check

With auth enabled, a user who may not read a key attached to a lease is refused `LeaseLeases` and
`LeaseTimeToLive(lease, WithAttachedKeys())`. But while a member is restoring a snapshot sent by the
leader, both requests sent to that member succeed: `LeaseLeases` lists the lease, and `LeaseTimeToLive`
with keys returns the name of the key the user may not read. The member reloads the leases with no
keys attached before it re-attaches them, and both permission checks read the leases in between.

**Expected:** with auth enabled, `LeaseLeases` and `LeaseTimeToLive` with `Keys` should refuse a user
who may not read a key attached to a lease (`checkLeaseLeases`, `checkLeaseTimeToLive`: "check RBAC
permission only if Keys is true",
[`v3_server.go#L708`](https://github.com/etcd-io/etcd/blob/4e090c033abc29636df2f844fbdd363adffcd90b/server/etcdserver/v3_server.go#L708)),
as they do outside the restore, whichever member receives the request.

**Impact:** clusters with auth enabled where a non-admin user may not read every key attached to
leases, and a member falls far enough behind to be sent a snapshot (a partition, a restart after
downtime, a slow disk; with the default snapshot settings).
The window is the member's key-value index restore, which grows with the number of key revisions in
the store (about 200 ms with 192k keys in the test). What leaks: from `LeaseTimeToLive` with
keys, the names of the keys attached to the lease (not their values); from `LeaseLeases`, the IDs of
all leases, which etcd otherwise refuses to list to this user. No crash, no write.

**Reproduction:** `TestV3LeaseAuthDuringSnapshotRestore` in
[`issues/etcd-lease-auth-snapshot-restore-keyless/v3_lease_auth_snapshot_restore_test.go`](etcd-lease-auth-snapshot-restore-keyless/v3_lease_auth_snapshot_restore_test.go),
copied into `tests/integration` at etcd-io/etcd@4e090c033abc29636df2f844fbdd363adffcd90b
(2026-11-24), go1.27.4 linux/amd64, no failpoint. Three members, auth on; user `u` may read `a/`
only; root's lease `Lz` holds `z/lease`, plus 1500 transactions of 128 keys (to make the restore
take long enough); `u`'s client is on a follower F, where both requests are refused. F is
partitioned while the leader writes past its log compaction, then healed, so F restores a
snapshot; `u` sends both requests to F in a loop meanwhile. It failed in 4 runs out of 4:

```
$ go test ./integration/ -run '^TestV3LeaseAuthDuringSnapshotRestore$' -count=1 -v
    v3_lease_auth_snapshot_restore_test.go:137: Leases at F answered u: 1 leases
    v3_lease_auth_snapshot_restore_test.go:137: Leases at F answered u: 1 leases
    v3_lease_auth_snapshot_restore_test.go:155: TimeToLive(Lz, keys) at F answered u: keys ["z/lease"]
    v3_lease_auth_snapshot_restore_test.go:155: TimeToLive(Lz, keys) at F answered u: keys ["z/lease"]
    v3_lease_auth_snapshot_restore_test.go:172:
        	Error:      	Should be zero, but was 2
        	Messages:   	Leases answered a user who may not read a key attached to a listed lease
    v3_lease_auth_snapshot_restore_test.go:173:
        	Error:      	[]string{"z/lease", "z/lease"} should not contain "z/lease"
        	Messages:   	TimeToLive with keys returned a key the caller may not read
    v3_lease_auth_snapshot_restore_test.go:174:
        	Error:      	Should be zero, but was 2
        	Messages:   	TimeToLive with keys answered a user who may not read the lease's key
--- FAIL: TestV3LeaseAuthDuringSnapshotRestore (27.44s)
FAIL	go.etcd.io/etcd/tests/v3/integration	27.479s
```

(A run with more concurrent requests once crashed F instead, in `IsAdminPermitted` right after the
restore: `issues/etcd-auth-snapshot-closed-backend-panic.md`, a different bug.)

**Cause:** `applySnapshot` calls
[`lessor.Recover`](https://github.com/etcd-io/etcd/blob/4e090c033abc29636df2f844fbdd363adffcd90b/server/etcdserver/server.go#L1067),
which reloads every lease with an empty key set
([`initAndRecover`](https://github.com/etcd-io/etcd/blob/4e090c033abc29636df2f844fbdd363adffcd90b/server/lease/lessor.go#L820-L826)),
then [`kv.Restore`](https://github.com/etcd-io/etcd/blob/4e090c033abc29636df2f844fbdd363adffcd90b/server/etcdserver/server.go#L1074),
which re-attaches the keys only after it has read the whole key index
([`kvstore.go#L403-L413`](https://github.com/etcd-io/etcd/blob/4e090c033abc29636df2f844fbdd363adffcd90b/server/storage/mvcc/kvstore.go#L403-L413)).
[`checkLeaseLeases`](https://github.com/etcd-io/etcd/blob/4e090c033abc29636df2f844fbdd363adffcd90b/server/etcdserver/v3_server.go#L752-L784)
and [`checkLeaseTimeToLive`](https://github.com/etcd-io/etcd/blob/4e090c033abc29636df2f844fbdd363adffcd90b/server/etcdserver/v3_server.go#L608-L635)
check `IsRangePermitted` on the keys the member's own lessor holds, which is none in that window, so
both pass. `LeaseLeases` then answers from that lessor; `LeaseTimeToLive` on a follower forwards to
the leader
([`leaseTimeToLive`](https://github.com/etcd-io/etcd/blob/4e090c033abc29636df2f844fbdd363adffcd90b/server/etcdserver/v3_server.go#L637-L697)),
whose lessor has the keys, and returns its answer, keys included, with no check of the keys it
returns.

## Proof

yes: the dist theorem `etcd_safe_nocrash` runs with snapshots on and auth on (`authLease`), and its
workload `foreign` (`examples/etcd/dist/client/authlease.go`) checks only what holds in this window:
a refused `Revoke`, `LeaseTimeToLive` with keys returning no key the caller may not read (true only
with the verified fork's re-check of the returned keys, `checkLeaseTimeToLiveKeys` at `d26dd5da6`,
`Lease_TimeToLiveOn_dist`), and nothing of `LeaseLeases`. The single-process `etcd_authlease` asserts
both refusals, so the multi-machine theorem does not subsume it (rule 41; `notes/etcd-dist-f7-fork.md`).

## Fix

Not written. `LeaseTimeToLive`: check permission on the keys actually returned (as for
`issues/etcd-lease-timetolive-keys-toctou.md`); on a follower that refuses the leaked key, though a leader restoring a snapshot can still answer from its half-restored
lessor. For both requests and the window itself: hold the lessor out of service until the keys are
re-attached (attach the keys inside `Recover`, or block lease reads on a flag `applySnapshot` clears
after `kv.Restore`), so that no check sees a lease without its keys.

## Notes

The leader can be in the same window (a member elected while it restores a snapshot), where
`LeaseTimeToLive` answers from its own lessor: usually `ErrLeaderChanged` (a reloaded lease is
demoted), not always (`nonissues/etcd-lease-keys-mid-apply.md`, "A second window"); not tested here.
Upstream's threat model treats RBAC as a secondary control; this leaks key names and lease IDs, not
values, so it is a hardening report, not a security one.
