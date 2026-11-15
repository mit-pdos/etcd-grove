---
upstream: known
checked: 2026-11-14
links:
  - etcd-io/etcd#22747 issue open: this finding (both panic sites, reproduced on main)
  - etcd-io/etcd#22806 pr open: length check in unsafeReadAuthRevision (site 2 only)
blocks-proof: no
---

# auth: `NewAuthStore` panics on a malformed `authUsers` value or a short `authRevision`

At startup `NewAuthStore` reads the auth buckets through the backend's batch transaction:
`unsafeGetAllUsers` (`server/storage/schema/auth_users.go`) calls `lg.Panic` when a user value does
not unmarshal, and `unsafeReadAuthRevision` (`server/storage/schema/auth.go:137-144`) calls
`binary.BigEndian.Uint64` on the `authRevision` value without checking that it is 8 bytes.

**Why not an issue:** etcd writes only encoded users (`proto.Marshal`) and 8-byte revisions
(`commitRevision`), so the input is a damaged or foreign backend file (a corrupted data dir, or
`etcdutl snapshot restore` of such a snapshot). etcd's threat model leaves disk contents to the
operator. Robustness, not a reachable bug in etcd's own use. Reported upstream with
reproducers (#22747).

## Proof

no: the startup path's spec is `auth.NewAuthStore.spec` (a trust-boundary axiom's), whose premise fixes the auth
buckets to `∅`/`authBoot` with no users or roles; the verified readers take `schema.revWf` and
`schema.usersWf` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvAuthBackend.lean`), which every
image etcd writes satisfies. A corrupt file is outside the storage model. (Found by the bug triage
of 2026-11, branch `bug-triage/auth-2026-11`, `notes/bug-triage/etcd-22747.md`, not on `lean`.)
