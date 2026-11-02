---
upstream: none
checked: 2026-11-02
links: []
blocks-proof: no
---

# auth: a role or user record grown past bbolt's value limit makes every member exit while applying a grant

`RoleGrantPermission` appends the permission to the role and puts the whole role record
(`UserGrantRole` likewise the user): each grant is within the 1.5 MiB request limit, but about 1400
grants of a permission with a 1.5 MiB key to one role make the record exceed bbolt's
`MaxValueSize` (2 GiB), and the next grant's put fails, which the backend treats as fatal on every
member, and again on replay.

**Why not an issue:** no test (it needs about 2 GiB of grants by an admin); found by code reading.

## Proof

no: the top-level adequacy proof needs no fix on the goosed fork for it; `auth.NewAuthStore`'s axiom takes the premise `authRecordsFit`
(`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvBoot.lean`), a premise of `NewServer.spec` that
etcd does not enforce.

## Notes

The single-request case of the same fatal write is `etcd-backend-put-value-too-large-fatal`, the
key case `issues/etcd-auth-useradd-long-name-fatal.md`. A test that builds such a role (slow, 2 GiB
of disk) could promote it. The 2026-10-23 review's plan: skip for now. A fix would bound a role's
permissions (or a user's roles) with an error.
