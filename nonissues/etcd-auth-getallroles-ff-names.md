---
upstream: none
checked: 2026-11-12
links: []
blocks-proof: no
---

# storage/schema: `GetAllRoles` skips a role whose name starts with the byte `0xff`

`unsafeGetAllRoles` (`server/storage/schema/auth_roles.go:91`) ranges the `authRoles` bucket from
`[]byte{0}` to `[]byte{0xff}`, and the batch transaction's `unsafeRange` keeps keys below the end
(`server/storage/backend/batch_tx.go:211-212`). A role named `"\xff"` (or any name whose first byte
is `0xff`), stored by `UnsafePutRole`, is found by `GetRole` but missing from `GetAllRoles`, so
`RoleList` does not list it. Found by S0 of the `etcd_auth_safe` Scope (the axiom review of
`authSchemaSrv`), Go test `TestS0GetAllRolesMissesFFRole` against the real `schema`/`backend`
packages (`/shared/tmp/auth-safe/s0/tests/zz_authschemasrv_test.go`, at the fork pin `c90b03b56`).

**Why not an issue:** etcd never stores such a name: role names arrive in gRPC requests, whose
proto3 `string` fields protobuf-go rejects unless they are valid UTF-8, and valid UTF-8 never holds
the byte `0xff`. The test writes through the schema package directly, as no etcd caller does.

## Proof

No. `GetAllRoles`' clause of the trusted read contract (`auth.rolesOut`,
`Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean`) promised every role of the state, which this
falsified (S0's F3, `notes/auth-schema-srv-refuted.md`); since auth-schema-fix it promises the roles
whose name is non-empty and below `"\xff"` (`auth.roleListed`), and `RoleList`'s reply
(`roleListOut`) lists those.

## Notes

A fix would range to the end of the bucket (`UnsafeForEach`, as `unsafeGetAllUsers` does).
