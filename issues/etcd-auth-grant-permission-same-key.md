---
upstream: unchecked
checked: 2026-10-27
links: []
---

# `RoleGrantPermission` appends instead of updating when another permission with the same key sorts first

- **Status**: a bug (a wrong result, in authorization). Granting a permission on a range a role
  already has is meant to update that permission's type ("update existing permission"), but the
  lookup finds the first permission with the same key, and only if that one has the same range
  end is it updated; otherwise the new permission is appended. When the role has two permissions
  with one key and different range ends, the grant appends a duplicate of the range, and the old
  type stays in effect: setting `[a, c)` from `READWRITE` to `READ` leaves writes to `[a, c)`
  permitted. Which entry the lookup meets depends on the record's order among equal keys
  (`permSlice` compares keys only; `sort.Sort` is unstable), so the outcome is not determined by
  the role's set of permissions. Needs an admin (auth on) or any client (auth off) to make the
  grants, and two permissions sharing a key.
- **Where**: at the etcd pin of `etc/goose.py` (`c00a2dc06`): `server/auth/store.go:830`
  (`authStore.RoleGrantPermission`: `sort.Search` on `Key` alone, then
  `bytes.Equal(...RangeEnd, r.Perm.RangeEnd)` at line 834 on that one index; else `append` and
  `sort.Sort(permSlice(...))` at lines 845-846); `server/auth/store.go` `permSlice.Less`
  (`bytes.Compare(Key)` only). `RoleRevokePermission` removes every match, so revoking and
  granting again works around it.
- **What happens**: reproduced by
  [`etcd-auth-grant-permission-same-key/grant_same_key_test.go`](etcd-auth-grant-permission-same-key/grant_same_key_test.go)
  (package `auth`; at the pin, run with `go test -overlay` mapping it into `server/auth/`, using
  `store_test.go`'s `setupAuthStore`): grants `("a", "", READ)`, `("a", "c", READWRITE)`, then
  `("a", "c", READ)`; the role then holds three permissions, `("a", "c", READWRITE)` and
  `("a", "c", READ)` both, and `IsPutPermitted` of `"b"` for a user with the role succeeds.
  Output: `perm "a" "" READ`, `perm "a" "c" READWRITE`, `perm "a" "c" READ`, `put of b permitted
  after [a, c) was set to READ (3 permissions)`.
- **Expected**: the code's own comment (`// update existing permission`) and `etcdctl role
  grant-permission`'s documentation ("Grants a key to a role"; granting again changes the type):
  one permission per range, with the last granted type.
- **How the proof handles it**: the auth model's step `auth.roleGrantPermissionR`
  (`Proof/go_etcd_io/etcd/server/v3/auth/Steps.lean`) allows both outcomes (some permutation of
  the permissions with the new one, or the entry on the range replaced), so the authorization
  results hold of either; it is also why the step is not determinate and the admin proposal path
  with auth on leaves `RoleGrantPermission` out (`notes/decisions.md`, "E3z of the auth plan").
- **Possible fixes**: search for an entry with the same key and range end among those with the
  key (scan from `idx` while the key is equal), or sort by key then range end (`permSlice.Less`)
  so that `sort.Search` on the pair finds it; either makes the outcome a function of the set of
  permissions.
- **Found**: 2026-10-27, designing the determinacy of `RoleGrantPermission`'s model step for the
  auth plan's E3z (reading `store.go`), reproduced the same day.
