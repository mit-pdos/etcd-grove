---
upstream: none
checked: 2026-10-21
links:
  - etcd-io/etcd#10710 pr merged: related, not this bug (the lease benchmark's Revoke left leases in leaseMap until the PR set a fake range deleter; a reviewer noted it, the lessor was not changed)
blocks-proof: no
---

# lease: without a range deleter, `Revoke` keeps the lease and a second `Revoke` panics

When no range deleter is set, `lessor.Revoke` returns nil before removing the lease from its map
and the backend, though the `Lessor` interface says the lease is revoked; a second `Revoke` of it
closes `revokec` again and panics (`close of closed channel`).

**Why not an issue:** a precondition etcd meets: the server's `mvcc.New` sets the range deleter
before any revocation; only a lessor used without a store hits it (documentation at most).

## Proof

no: `Revoke` is unproved; the apply package's lessor contract is about the server's lessor, whose
range deleter is set.

## Notes

The test,
[`nonissues/etcd-lessor-revoke-twice-no-deleter/revoke_no_deleter_test.go`](etcd-lessor-revoke-twice-no-deleter/revoke_no_deleter_test.go)
(`server/lease`), fails at etcd-io/etcd@1573d5941 (go1.27.3): `after Revoke(1) returned nil, the
lease is still there` and `second Revoke(1) panicked: close of closed channel`. INDEX-reviewed.md's
plan: skip for now.
