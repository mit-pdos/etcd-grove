---
upstream: none
checked: 2026-11-12
links: []
blocks-proof: no
---

# etcd: `schema.ReadStorageVersionFromSnapshot` panics on a database with no `meta` bucket

`ReadStorageVersionFromSnapshot(tx)` (`server/storage/schema/version.go:48-55`) calls
`tx.Bucket(Meta.Name()).Get(MetaStorageVersionName)` without checking the bucket: in a bbolt file
with no `meta` bucket, `tx.Bucket` returns nil and `Get` on the nil `*Bucket` dereferences it
(bbolt `bucket.go:435`, `b.Cursor()`), a nil-pointer panic instead of a nil version.

**Why not an issue:** found by code reading, no test; its only caller is `etcdutl snapshot status`
(`etcdutl/snapshot/v3_snapshot.go:140`), on a file that is not an etcd database (every etcd backend
creates `meta` at boot), outside the server.

## Proof

no: the server never calls it; no proved or planned server spec reaches it.

## Notes

Found 2026-11-12 by the spec plan's bbolt review (completeness, etcd's callers), at etcd `a4d2bb17`.
