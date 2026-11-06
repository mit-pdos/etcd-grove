---
upstream: none
checked: 2026-11-06
links:
  - etcd-io/etcd#20729 pr merged: related, not this (the request-id generator's comment)
blocks-proof: no
---

# etcdserver: LeaseGrant without an ID fails with "lease already exists" when two members' IDs agree in the low 15 bits

A client's `Grant` (no lease ID given, the server picks one) can fail with `etcdserver: lease
already exists` in a cluster where two members' IDs agree in their low 15 bits: both members
choose lease IDs from the same range, so one member eventually picks the ID of a lease the other
granted. If that earlier lease has since been revoked or expired, the new lease silently gets
the old lease's ID instead.

**Expected:** a `Grant` with no ID should not fail because the ID the server chose is taken, as
the API states that "If ID is set to 0, the lessor chooses an ID"
([`rpc.proto`](https://github.com/etcd-io/etcd/blob/cda871cc952195664ebec450b77709c12f2d2a88/api/etcdserverpb/rpc.proto#L878)) and
client/v3's `Lease.Grant` documents only "Grant creates a new lease".

**Impact:** any cluster of two or more members, default configuration, where two member IDs (a
hash of the peer URLs and cluster token, plus the time for a member added later) agree in the low
15 bits but not the 16th: about 1 in 22000 three-member clusters (3 pairs × 2^-16; agreeing in
all 16 bits, another 1 in 22000, collides request IDs too). Each member replacement draws a new
ID. Within such a pair, the member that started earlier picks the other's lease IDs once it has
taken 256 more IDs (two per `Grant`, one per other write) per millisecond of start-time
difference than the other member, which is reached quickly when the members were started
together (e.g. a cluster bootstrapped at once) and clients favor one of them. The mask and
generator are the same on `main` and `release-3.4` to `release-3.6`.

**Reproduction:** `TestLeaseGrantNoIDCollidesAcrossMembers` in
[`issues/etcd-lease-id-mask-member-prefix/v3_lease_id_collision_test.go`](etcd-lease-id-mask-member-prefix/v3_lease_id_collision_test.go),
copied into `tests/integration` at etcd-io/etcd@cda871cc952195664ebec450b77709c12f2d2a88 (2026-11-05), go1.27.3 linux/amd64. It
picks the integration framework's listener counter so that the peer URLs give two of three
members IDs agreeing in the low 15 bits only (checking the IDs after start), grants one lease
through each, a few more through the member whose IDs are ahead, then grants through the other
until it passes them:

```
$ go test ./integration -run TestLeaseGrantNoIDCollidesAcrossMembers -count=1 -v
    v3_lease_id_collision_test.go:88: members 1 and 2 have IDs bc83d412d4ce57bf and b899ec9e214ed7bf
    v3_lease_id_collision_test.go:111: first leases 57bfa1ae94e52c02 (member 1) and 57bfa1ae94e52503 (member 2): member 2 is 1791 IDs behind
    v3_lease_id_collision_test.go:147: Grant without an ID through member 2 failed: etcdserver: lease already exists (the ID it chose is a lease granted through member 1)
--- FAIL: TestLeaseGrantNoIDCollidesAcrossMembers (1.22s)
FAIL	go.etcd.io/etcd/tests/v3/integration	1.262s
```

It failed in 10 of 10 runs (when the members happen to start in the same millisecond, the first
two grants already collide).

**Cause:** `LeaseGrant` picks `reqIDGen.Next() & (1<<63 - 1)`
([`v3_server.go:439`](https://github.com/etcd-io/etcd/blob/cda871cc952195664ebec450b77709c12f2d2a88/server/etcdserver/v3_server.go#L439)).
The generator keeps a member's IDs apart from other members' only through its prefix, the
member ID's low 16 bits in bits 48–63
([`idutil/id.go:57`](https://github.com/etcd-io/etcd/blob/cda871cc952195664ebec450b77709c12f2d2a88/pkg/idutil/id.go#L57)),
and starts its suffix at the start time in milliseconds × 256. The mask clears bit 63, the
prefix's top bit, so lease IDs are kept apart by only 15 bits of the member ID, and a member
started earlier walks into the other's range.

## Proof

no: in the revocable mode the proof boots a single member (`srvMemberBoot_alloc`'s `hpfx`,
`kvGrantIds`' one prefix, `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRequest.lean`), and in
the monotone mode an id collision is the `ErrLeaseExists` the specs allow. A multi-member revocable
cluster (the lease plan's step 2) would need a premise that the members' ids differ in the low
15 bits, or a per-prefix ever-set.

## Fix

Not written. Options: choose the lease ID when the grant is applied (the lessor picks an unused
ID), or keep the member prefix whole (e.g. clear a suffix bit instead of bit 63, with the prefix
in bits 47–62), or reject at bootstrap and member add an ID agreeing with another member's in the
low 16 bits (which also covers the request-ID collision).

## Notes

Found by code reading (the scope of the multi-member lease example, 2026-11-06), first recorded
as a non-issue for want of a test. The request-ID analogue, with all 16 bits equal, is
[`../nonissues/etcd-request-id-member-prefix.md`](../nonissues/etcd-request-id-member-prefix.md).
The test steers the framework's `UniqueCount` only to choose the peer URLs; an operator choosing
those URLs gets the same member IDs.
