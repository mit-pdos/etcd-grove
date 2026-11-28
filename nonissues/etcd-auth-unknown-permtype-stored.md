---
upstream: none
checked: 2026-11-27
links: []
blocks-proof: no
---

# auth: `RoleGrantPermission` stores a permission of an unknown type, which only `RoleRevokePermission` sees

`RoleGrantPermission` accepts and stores a permission whose `PermType` is not READ, WRITE or
READWRITE (protobuf enums are open, and no layer checks the value): `{Key: "k", PermType: 7}` is
stored in the role. Every access check ignores it: the range-permission cache's build switches on
the three known types and skips the rest. `RoleRevokePermission`, however, matches on
`(Key, RangeEnd)` whatever the type. A role holding only that permission and a role holding none
therefore grant the same accesses, but revoking `k` succeeds (and bumps the auth revision) on
the first and fails with `ErrPermissionNotGranted` (no bump) on the second.

**Why not an issue:** a stored permission no check ever uses and that a revoke can remove is
harmless; etcd documents no validation of the type. Found while modelling the auth store.

Measured: `TestD3RevokeUnknownTypedPermission` in
[`etcd-auth-unknown-permtype-stored/unknown_permtype_test.go`](etcd-auth-unknown-permtype-stored/unknown_permtype_test.go),
copied into `server/auth` at the pinned fork commit upamanyus/etcd@d7c7f6434abc (the `server/v3`
replace of `examples/go.mod`), go1.27.3: passes (grant stored, revoke on that role succeeds with
revision +1, revoke on the empty role returns `ErrPermissionNotGranted` with the revision unchanged).

Sites (at d7c7f6434abc): grant stores `r.Perm.PermType` unchecked (`server/auth/store.go:839-845`);
revoke filters on `Key`/`RangeEnd` only (`store.go:699-707`); the cache's build ignores unknown
types (`range_perm_cache.go:53-63`, the `switch perm.PermType` with READWRITE, READ, WRITE cases
and no default); the checks take only READ or WRITE (`range_perm_cache.go:87-90, 100-103`;
`store.go:904-912`).

## Proof

no: the auth model keeps a role's stored wire permissions, unknown types included (2026-11-27
decision, option 1 of the D3 blocker in `notes/nomode-n1.md`); the access checks and the tree
build skip unknown types exactly where Go does, so grant and revoke are functions of the model's
state. Before that change the model dropped unknown types, and `RoleRevokePermission` could not be
modelled by a step function.
