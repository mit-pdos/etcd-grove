---
upstream: known
checked: 2026-11-02
links:
  - etcd-io/etcd#21845 pr open: same bug and fix (scan the same-key entries for the exact `(Key, RangeEnd)` pair before appending), by an outside contributor, 2026-05-29; labeled `stale` and `needs-ok-to-test`, no review; its unit test (`TestRoleGrantPermissionSameKeyDifferentRangeEnd`) checks the re-grant replaces the type, not the permission check
blocks-proof: yes
---

# auth: re-granting a permission on a range does not change its type when the role has another permission with the same start key

When a role has two permissions starting at the same key (say read on `a`, and read-write on
`[a, c)`), granting `[a, c)` again with a new type adds a duplicate permission instead of updating
the existing one, so the old type stays in effect: downgrading `[a, c)` from `READWRITE` to `READ`
leaves writes to `[a, c)` permitted.

**Expected:** granting a permission on a range the role already has should replace that
permission's type, as the code's own `// update existing permission` branch intends and as
[`etcdctl role grant-permission`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/etcdctl/README.md#L1330-L1332)
("grants a key to a role") is used to change a role's access.

**Impact:** clusters with auth enabled whose admin gives a role two permissions with the same start
key and different range ends, then changes the type of one of them. A downgrade silently does not
take effect (the role keeps write access); revoking the permission and granting it again works.
Admin-only, and needs that shape of permissions; all releases with this code.

**Reproduction:** `TestRoleGrantPermissionSameKeyNoUpdate` in
[`issues/etcd-auth-grant-permission-same-key/grant_same_key_test.go`](etcd-auth-grant-permission-same-key/grant_same_key_test.go),
copied into `server/auth` at etcd-io/etcd@1573d5941 (2026-10-28), go1.27.3 linux/amd64. It makes
the three grants on the auth store as the apply loop does for `RoleGrantPermission` requests, then
checks a put on `b` for a user with the role:

```
$ go test ./auth -run '^TestRoleGrantPermissionSameKeyNoUpdate$' -count=1 -v
=== RUN   TestRoleGrantPermissionSameKeyNoUpdate
    grant_same_key_test.go:36: perm "a" "" READ
    grant_same_key_test.go:36: perm "a" "c" READWRITE
    grant_same_key_test.go:36: perm "a" "c" READ
    grant_same_key_test.go:43: put of b permitted after [a, c) was set to READ (3 permissions)
--- FAIL: TestRoleGrantPermissionSameKeyNoUpdate (0.00s)
FAIL
```

**Cause:** [`RoleGrantPermission`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/auth/store.go#L825-L842)
binary-searches the role's permissions by key only and updates the entry it lands on only if that
one also has the same range end; otherwise it appends. The permissions are sorted by key alone
([`permSlice.Less`](https://github.com/etcd-io/etcd/blob/1573d59416efa220421c451f5266b24a5d8374ef/server/auth/store.go#L800-L802)),
so when another permission with the same key comes first, the matching one is never found.

## Proof

yes: the verified fork replaces every permission on the range (`acafa0317`, `etc/goose.py`); the
auth model's step allows both outcomes (`Proof/go_etcd_io/etcd/server/v3/auth/Steps.lean`,
`roleGrantPermissionR`).

## Fix

Look for an entry with the same key and range end among all those with the key (scan from the
search index while the key is equal), as #21845 does, or sort by key then range end so the search
finds it.

## Notes

The test calls the auth store directly, as the applier does; an integration test through
`clientv3`'s `RoleGrantPermission` would be the form to file.

#21845 (open, stale, unreviewed, no issue of its own) has the fix and a unit test of the re-grant,
but no issue states the impact (a downgrade leaves write access), so the report stays whole here.
Filing would be this report as an issue linking #21845, to get it reviewed.
