---
upstream: none
checked: 2026-11-12
links: []
blocks-proof: no
---

# storage/schema: `UnsafePutUser` panics on a role name that is not valid UTF-8

`authpb.User.roles` is a proto3 `repeated string` (`api/authpb/auth.proto:14`). protobuf-go's
`Marshal` refuses a string field that is not valid UTF-8, and `UnsafePutUser`
(`server/storage/schema/auth_users.go:41-44`) then calls `lg.Panic`. So
`UnsafePutUser(&authpb.User{Name: "u", Roles: []string{"\xff"}})` panics. Found by S0 of the
`etcd_auth_safe` Scope, Go test `TestS0PutUserInvalidUTF8RolePanics`
(`/shared/tmp/auth-safe/s0/tests/zz_authschemasrv_test.go`, fork pin `c90b03b56`).

**Why not an issue:** etcd never puts such a user: a user's roles come from `UserGrantRole`
requests, which arrive through gRPC and the raft log as protobuf messages, and protobuf-go's
`Unmarshal` rejects a proto3 `string` that is not valid UTF-8 (so `pbutil.MustUnmarshalMessage`
panics on such an entry before the store sees it; Go test
`/shared/tmp/auth-safe/fix-tests/irr_utf8_test.go`). The S0 test calls the schema package
directly, as no etcd caller does.

## Proof

No. The trusted write contract's `UnsafePutUser` clause (`authBatchTxLkR`, `authBatchTxLk`,
`Proof/go_etcd_io/etcd/server/v3/auth/InvAuth.lean`) asked only for sorted roles and a name that
fits a key, which this falsified (S0's F4, `notes/auth-schema-srv-refuted.md`); since
auth-schema-fix it also asks for valid UTF-8 roles, which the proved store supplies from the
decoded request (`apply.irrDecode`'s UTF-8 law) and the state's invariant.
