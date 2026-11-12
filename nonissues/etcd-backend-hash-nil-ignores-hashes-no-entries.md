---
upstream: none
checked: 2026-11-12
links:
blocks-proof: no
---

# backend: `Hash(nil)` hashes only the bucket names, and the backend's defrag tests compare it

`backend.Hash(ignores)` writes an entry into the CRC only when `ignores != nil && !ignores(bucket,
key)` (`server/storage/backend/backend.go:439`): with a nil filter, no entry is hashed, only the
bucket names. The `Backend` interface does not document the filter (a reader expects nil to mean
"ignore nothing"). etcd's own tests read it so: `backend_test.go:163`, `:173` (`TestBackendDefrag`:
`Hash(nil)` before and after `Defrag`, "db hash changed after defrag") and `:320` (the non-blocking
defrag test, comparing two backends' `Hash(nil)`) check nothing about the entries: a Defrag that lost
or changed entries would pass them.

**Why not an issue:** no caller in etcd passes nil (the only one, mvcc's `store.Hash`,
`storage/mvcc/kvstore.go:161`, passes `schema.DefaultIgnores`), so it is a documentation gap and a
test weakness, not a wrong result. Found by code reading while writing the backend's requirement
snippets (`examples/specreq/backend/`), 2026-11-12.

## Proof

no: no etcd path calls `Hash(nil)`, and nothing in etcd relies on the hash's value (the Hash RPC
returns it to its client); the backend's snippets call `Hash(schema.DefaultIgnores)` only for its
not panicking.

## Notes

A fix would either hash every entry when `ignores` is nil (and make the tests meaningful) or document
the filter's meaning on the interface. The tests could pass a filter that ignores nothing.
