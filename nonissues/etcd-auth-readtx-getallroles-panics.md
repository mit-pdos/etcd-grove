---
upstream: none
checked: 2026-11-02
links: []
blocks-proof: no
---

# storage/schema: `UnsafeGetAllRoles` on the auth backend's read transaction always panics

`(*authReadTx).UnsafeGetAllRoles` ranges the `authRoles` bucket with no limit through a
`backend.ReadTx`, whose `UnsafeRange` panics ("do not use unsafeRange on non-keys bucket") on a
multi-key range of any bucket but the key bucket. The `AuthReadTx` interface lists it like
`UnsafeGetAllUsers`, which works.

**Why not an issue:** no caller in etcd: the auth store's `GetAllRoles` goes through the batch
transaction (`authBatchTx.UnsafeGetAllRoles`, which works); dead code behind an interface method.
No test, found by code reading.

## Proof

no: the read side is proved over point reads only; `authReadTx.UnsafeGetAllRoles` is translated
and not specified (`etc/link-lean-first-server.txt`); the read transaction's `UnsafeRange` spec
has the panic as a premise.

## Notes

A fix would iterate with `UnsafeForEach` as `unsafeGetAllUsers` does, or drop the method from
`AuthReadTx`.
