---
upstream: none
checked: 2026-11-06
links:
  - etcd-io/etcd#20729 pr merged: related, not this (the request-id generator's comment); no duplicate found 2026-11-06
blocks-proof: no
---

# etcdserver: Grant without an ID fails with "lease already exists" when two members' IDs agree in their low 15 bits

In a cluster where two members' IDs agree in their low 15 bits, a `Grant` without a lease ID
through one of them can fail with `etcdserver: lease already exists`, having chosen the ID of a
lease granted through the other. If that lease was revoked, the new lease silently reuses its ID.
This affects any client granting leases without an ID through both members.

**Expected:** a `Grant` without an ID should not fail because the ID the server chose is taken
(`rpc.proto`: "If ID is set to 0, the lessor chooses an ID").

**Impact:** about 1 in 11000 three-member clusters have two such members (each member
replacement draws a new ID). The member started earlier reaches the other's lease IDs once it has
served about 256 more requests per millisecond between their start times: soon, when clients favor
it. Retrying the `Grant` works around it.

**Reproduction:** `TestLeaseGrantNoIDCollidesAcrossMembers` in
[`issues/etcd-lease-id-mask-member-prefix/v3_lease_id_collision_test.go`](etcd-lease-id-mask-member-prefix/v3_lease_id_collision_test.go),
at `main` (etcd-io/etcd@cda871cc952195664ebec450b77709c12f2d2a88), go1.27.3 linux/amd64. It chooses
peer URLs giving two of three members such IDs, grants leases through both, then through the member
whose lease IDs are behind until they pass the other's. It fails (output trimmed):

```
$ go test ./integration -run TestLeaseGrantNoIDCollidesAcrossMembers -count=1 -v
    v3_lease_id_collision_test.go:84: members 1 and 2 have IDs 825843e0dde7daed and 66dc958e35bc5aed
    v3_lease_id_collision_test.go:107: first leases 5aeda1aeada1e702 (member 1) and 5aeda1aeada1e703 (member 2): member 1 is 1 IDs behind
    v3_lease_id_collision_test.go:143: Grant without an ID through member 1 failed: etcdserver: lease already exists (the ID it chose is a lease granted through member 2)
--- FAIL: TestLeaseGrantNoIDCollidesAcrossMembers (0.22s)
FAIL
FAIL	go.etcd.io/etcd/tests/v3/integration	0.261s
```

It failed in every run.

**Cause:** when the request has no ID, `LeaseGrant` chooses `reqIDGen.Next()` with bit 63 cleared
([`v3_server.go#L436-L440`](https://github.com/etcd-io/etcd/blob/cda871cc952195664ebec450b77709c12f2d2a88/server/etcdserver/v3_server.go#L436-L440)).
The generator keeps one member's IDs apart from another's only by its prefix, the member ID's low 16
bits in bits 48-63 ([`id.go#L57`](https://github.com/etcd-io/etcd/blob/cda871cc952195664ebec450b77709c12f2d2a88/pkg/idutil/id.go#L57)), and starts the rest at the
start time in milliseconds times 256 ([`id.go#L59`](https://github.com/etcd-io/etcd/blob/cda871cc952195664ebec450b77709c12f2d2a88/pkg/idutil/id.go#L59)). Clearing
bit 63 leaves 15 bits of the member ID, so a member started earlier walks into the lease IDs of a
member whose ID agrees with its own in those bits, and the lessor rejects a grant whose ID is taken
([`lessor.go#L297-L299`](https://github.com/etcd-io/etcd/blob/cda871cc952195664ebec450b77709c12f2d2a88/server/lease/lessor.go#L297-L299)).

## Proof

no: in the revocable mode the proof boots a single member (`srvMemberBoot_alloc`'s `hpfx`,
`kvGrantIds`' one prefix, `Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRequest.lean`), and in
the monotone mode an id collision is the `ErrLeaseExists` the specs allow. A multi-member revocable
cluster (the lease plan's step 2) would need a premise that the members' ids differ in the low
15 bits, or a per-prefix ever-set.

## Fix

**Branch**: `fix/etcd-lease-id-mask-member-prefix` in `~/etcd-fixes/etcd-lease-id-mask-member-prefix` (upamanyus/etcd, not pushed): 58eb46756 test, e840fe4b6 fix
**Base**: etcd-io/etcd@cda871cc952195664ebec450b77709c12f2d2a88

**PR draft**:

Title: etcdserver: choose another lease ID when the chosen one is taken

For a grant without an ID, [`LeaseGrant`](https://github.com/etcd-io/etcd/blob/cda871cc952195664ebec450b77709c12f2d2a88/server/etcdserver/v3_server.go#L436-L440) takes one from the member's request ID generator and clears bit 63, assuming no other member takes it; but members whose IDs agree in their low 15 bits share that range, and the lessor [rejects](https://github.com/etcd-io/etcd/blob/cda871cc952195664ebec450b77709c12f2d2a88/server/lease/lessor.go#L297-L299) an ID taken by another member's lease. This PR proposes again with another ID when the ID the server chose is taken.

Fixes: the issue, once filed.

The first commit adds a test of the issue's example, which fails on `main`; the second, the fix, makes it pass.

**If a reviewer asks**:

- Why retrying is safe: the lessor checks the ID when the grant is applied and changes nothing when it
  is taken, so the rejected proposal left no lease; `LeaseGrant` then clears the ID and calls itself,
  which chooses a new ID, checks auth again and starts a new span with that ID. A client-chosen ID
  that is taken still fails with `ErrLeaseExists`. Each retry takes a new ID from the generator; the
  other member's leases take at most every other ID of the range (each request also takes one), so
  retries are rare (5 in the test's 2400 grants, run with a print on the retry path).
- Why not keep the whole member prefix (the one-line alternative): shifting the ID right by one
  maps two consecutive generator IDs to one lease ID, so a member's own concurrent grants collide;
  moving bit 63 into bit 47 (dropping the timestamp's top bit) keeps 16 bits but changes the lease
  ID layout, and still collides when two member IDs agree in all 16 bits (as likely as the 15-bit
  case it fixes). A separate lease ID generator has the same prefix problem. Rejecting such member
  IDs at bootstrap and member add does not help existing clusters.
- Why not check `s.lessor.Lookup` while choosing the ID (one more condition in the loop): it races
  with a grant of the same ID through the other member that is proposed but not yet applied here;
  the apply-time check is the only one every member agrees on. Not run.
- Why not choose the ID when the grant is applied: the entry would carry no ID, which members of
  the previous version apply differently (a mixed-version cluster during an upgrade).
- Not addressed by any of these: a new lease can still get the ID of a revoked or expired lease
  granted through the other member; the error was the visible part.
- History: the mask came with `9113a27bd` ("lease: grant consistent lease IDs", 2016-01), when the
  prefix was the member ID's low 8 bits; `e44e753e6` ("pkg/idutil: reduce conflict rate from 1% to
  0.005%", 2016-02) widened the prefix to 16 bits without revisiting the mask. #20729 (merged) fixed
  the generator's comment only; no issue or PR on this collision was found. The line is the same on
  `release-3.4` to `release-3.7`, so a backport applies.
- Why the test is not misuse: default configuration; the framework's listener counter only selects
  the peer URLs, which an operator choosing those URLs gets the same member IDs from. The test takes
  a few seconds to tens of seconds with the fix (it grants a little more than the gap between the
  two members' lease IDs; the gap is 256 IDs per millisecond between their starts).

**Verified** (go1.27.3 linux/amd64, 2026-11-06): at the tests commit the new test fails (output in
**Reproduction**); at the fix commit it passed in 4 of 4 runs (6-32s), and `server/lease/...`,
`server/etcdserver`, `tests/integration -run Lease` and `tests/integration/clientv3/lease` pass;
`gofmt -l` and `go vet` are clean.

## Notes

Found by code reading (the scope of the multi-member lease example, 2026-11-06), first recorded
as a non-issue for want of a test. The request-ID analogue, with all 16 bits equal, is
[`../nonissues/etcd-request-id-member-prefix.md`](../nonissues/etcd-request-id-member-prefix.md).
The test steers the framework's `UniqueCount` only to choose the peer URLs; an operator choosing
those URLs gets the same member IDs.
