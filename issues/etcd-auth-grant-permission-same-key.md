---
upstream: known
checked: 2026-10-17
links:
  - etcd-io/etcd#21845 pr open: the fix (scan the permissions with the same key for the range end); does not repair duplicates already stored (notes/pr-verify/etcd-21845.md)
---

# auth: `RoleGrantPermission` appends a duplicate instead of updating a permission whose key another one shares, so a downgrade has no effect

- **Status**: bug (a wrong result with a security effect: revoking write access by granting read on
  the same range silently keeps write access).
- **Where**: `server/auth/store.go` at the pinned revision (`etc/goose.py`, 09669450f; the same on
  upstream main b25719d10): `authStore.RoleGrantPermission` (`store.go:808-857`) binary-searches the
  role's `KeyPermission` for the first permission whose key is not less than the request's
  (`store.go:825-827`) and updates it only if *that* permission also has the request's range end
  (`store.go:829`); otherwise it appends. `KeyPermission` is sorted by key only (`permSlice.Less`,
  `store.go:800-802`), so a role can hold several permissions with one key, and the one the search
  finds is the first of them, not necessarily the one with the request's range end. The API
  (`etcdctl role grant-permission`, `AuthRoleGrantPermission`) documents granting as setting the
  permission on the range, which a later grant on the same range updates.
- **What happens**: with write on `[foo, fop)` and on `[foo, foq)`, granting read on `[foo, foq)`
  leaves three permissions, the write one on `[foo, foq)` still there; the permission cache is the
  union of them, so the user can still write `fop`. Reproduction (in `server/auth`):
  `notes/pr-verify/etcd-21845/store_grant_downgrade_test.go` on branch `pr-verify/etcd-21845`
  (`TestRoleGrantPermissionDowngradeSameKey`; fails at 09669450f: "write on fop still permitted
  after downgrading [foo, foq) to read", `notes/pr-verify/etcd-21845/downgrade-base.log`; passes
  with the PR). The PR's own test `TestRoleGrantPermissionSameKeyDifferentRangeEnd` shows the
  duplicate (3 permissions instead of 2).
- **How it happens**:
  1. `grant(W, [foo, fop))`: the role is `[W foo..fop]`.
  2. `grant(W, [foo, foq))`: the search finds index 0, whose range end is `fop`: append and sort,
     `[W foo..fop, W foo..foq]`.
  3. `grant(R, [foo, foq))`: the search finds index 0 again (`fop` ≠ `foq`): append,
     `[W foo..fop, W foo..foq, R foo..foq]`; `getMergedPerms` puts `[foo, foq)` in the write tree.
- **Expected**: the grant updates the permission on `[foo, foq)` to read.
- **How the proof handles it**: the old code is not verified (`RoleGrantPermission` was translated
  names-only); the spec written for the PR (`Spec/go_etcd_io/etcd/server/v3/auth/authStore__RoleGrantPermission.lean`,
  `GrantSpec` in `Proof/go_etcd_io/etcd/server/v3/auth/RolePerms.lean`) is what the old code fails
  and the PR's code meets (branch `pr-verify/etcd-21845`).
- **Possible fixes**: etcd-io/etcd#21845 (scan the permissions with the same key). A role already
  stored with two permissions on one range (by an etcd without the fix) keeps the stale one under
  that fix, which updates only the first: updating (or removing) every permission on the range
  would also repair those (`notes/pr-verify/etcd-21845/store_grant_existing_duplicate_test.go`).
  Revoking the range and granting again repairs a role today (`RoleRevokePermission` removes every
  permission on the range).
- **Found**: 2026-10-17, verifying etcd-io/etcd#21845 (`notes/pr-verify/etcd-21845.md`).
