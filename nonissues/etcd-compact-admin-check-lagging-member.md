---
upstream: none
checked: 2026-11-09
links: []
blocks-proof: no
---

# etcdserver: a user whose root role was revoked can still compact through a lagging member

With auth on, a compaction is allowed only for an administrator. That check runs on the member the
client talks to, against that member's own copy of the auth state, and is never repeated when the
compaction is applied. A member that has not yet applied the revocation of a user's root role
accepts that user's `Compact`, and every member then applies it.

**Expected:** an administrator-only request should be refused once the requester's root role is
revoked, as every auth-administration request is (the apply re-checks them:
`needAdminPermission`, `server/etcdserver/apply/auth.go:244`).

**Impact:** only with auth on, and only in the short window after a root role is revoked, through a
member that lags behind. The compaction succeeds instead of failing. It is a permission
race of the same kind as `etcd-doserialize-auth-enable-race.md`.

**Cause:** `kvServer.Compact` calls `aa.isPermitted(ctx)`, which is `IsAdminPermitted` on the
local auth store (`server/etcdserver/api/v3rpc/key.go:140`, `auth/store.go:915`). Then it
proposes `InternalRaftRequest{Compaction}`. `needAdminPermission` has no `Compaction` case, so the
apply does not re-check.

**Why not an issue:** found by reading (the 2a provability review, round 1, F8). There is no Go
test, and upstream was not searched.

## Proof

no: W0's model checks the compaction's administrator at an auth state the call saw (the member's
local view: W0's round 4), which is what the code does. A program that needs the stronger
guarantee assumes no revocation of a compacting user's root role (the snippet
`examples/specreq/v3rpc/kv.go`'s `ReqCompactAdmin`: "a user that never had the root role").

## Notes

The fix would add `r.Compaction != nil` to `needAdminPermission`, or re-check in
`applyCompaction`.
