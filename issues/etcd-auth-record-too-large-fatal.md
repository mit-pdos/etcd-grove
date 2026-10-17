---
upstream: unchecked
checked: 2026-10-17
links:
---

# A role or user record that outgrows bbolt's `MaxValueSize` makes every member exit while applying a grant

- **Status**: an unstated precondition; reachable with the default request size limit, by many
  requests (not reproduced: it needs about 2 GiB of grants).
- **Where**: at the etcd pin of `etc/goose.py` (`09669450f`): `server/auth/store.go`
  (`authStore.RoleGrantPermission` appends the permission to the role and puts the whole role,
  `tx.UnsafePutRole(role)`; `UserGrantRole` appends the role name to the user and puts the whole
  user); `server/storage/backend/batch_tx.go:169` (`unsafePut`: `lg.Fatal` on any error of bbolt's
  `Put`); bbolt v1.5.0 (`Put` returns `ErrValueTooLarge` above `MaxValueSize = (1 << 31) - 2`).
  The case of a single request is `issues/etcd-backend-put-value-too-large-fatal.md`.
- **What happens**: each grant is within the request size limit (1.5 MiB by default), but the
  record it is appended to grows without bound: about 1400 grants of a permission with a
  1.5 MiB key to one role make the role's encoding exceed `MaxValueSize`, and the next grant's
  put fails; the backend's `Fatal` exits the process, on every member, and again on replay.
- **Expected**: a bound on a role's permissions (or a user's roles), checked with an error, or
  stated.
- **How the proof handles it**: `auth.NewAuthStore`'s axiom (unit N4, 2026-10-17) takes the
  named premise `authRecordsFit` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvBoot.lean`):
  the auth store's records stay within the bound; a premise of `NewServer.spec`.
- **Possible fixes**: reject a grant whose resulting record would exceed the bound (or a fixed
  limit on the number of permissions per role and roles per user).
- **Found**: 2026-10-17, writing `auth.NewAuthStore`'s contract as an axiom true of the Go code
  (unit N4, D14d).
