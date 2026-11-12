---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# auth: a read can be refused with `ErrPermissionDenied` although it was permitted at every point of the call

With auth enabled, a `Range` (or read-only `Txn`) by a user whose role covers the key can fail with
`etcdserver: permission denied` while an `AuthDisable` and a `RoleRevokePermission` of that role are
applied concurrently, although at every moment of the call the read was permitted (first covered,
then auth off, then auth off and not covered).

**Why not an issue:** no test, found by code reading (verify round, A9-completeness F1, 2026-11-09).
The outcome is a refusal of a read whose permission was changing during the call, which a client
cannot distinguish from a refusal after the change; no state is corrupted. A test could show it with
a delay between `Revision()` and `lockedReadTx` in `isOpPermitted`.

**How:** `authStore.isOpPermitted` (`server/auth/store.go:862-901`) reads the enabled flag
(`IsAuthEnabled`, under `enabledMu`, released), then the revision, then the user under the
backend's read transaction, then the permission cache, each at the auth state it sees then. The flag
is read before the disable, the cache after the revoke.

## Proof

no: W0's model admits the denial over the check's three views (`State.deniedSince`,
`SpecPlan/Spec/go_etcd_io/etcd/api/v3/Model.lean`: the flag on at one auth table since the call's start, the
user not of the root role at a second, the range not covered at a third), which is what 3d's
`checkPost` gives.
