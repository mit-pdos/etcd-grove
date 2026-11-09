---
upstream: none
checked: 2026-11-09
links:
  - etcd-io/etcd#21909 pr open: related, not this bug (the auth revision check for verify-only JWT providers)
blocks-proof: yes
---

# auth: a read can return data written after the reader's permission was revoked, because the auth revision moves before the change is visible

With the simple token provider (etcd's default) or a client certificate, a serializable or
linearizable `Range` (and a read-only `Txn`, a `RangeStream`) can pass its permission check against
the users and roles as they were *before* an administrator's change (a revoked role, a revoked
permission, a deleted user), and then return a key written after that change, without
`ErrAuthOldRevision`.

**Why not an issue:** no test; found by code reading (the auth store's specs, 2026-11-09). The
window is the time between `commitRevision`'s `atomic.AddUint64` and the batch transaction's
`Unlock` inside one admin step: `refreshRangePermCache` runs in it, so it grows with the number of
users and roles. A test could promote it: a failpoint (or a sleep) in `refreshRangePermCache`, a
user reading a key during `UserRevokeRole` of its role, a put of the key right after.

**How:** every admin step bumps the store's revision atomic (`server/auth/store.go`,
`commitRevision`) before the batch transaction publishes the new users and roles to the read
transactions (`Unlock`'s write-back); the permission cache is refreshed in between. A reader's
`AuthInfo.Revision` is that atomic for a simple token (`tokenSimple.info` returns the revision it is
given, `authInfoFromToken`'s `as.Revision()`) and for a certificate (`AuthInfoFromTLS`). So a reader
can take revision `r` (the new one), pass `isOpPermitted`'s `revision < rev` test, and read the user
through `lockedReadTx` at the old state (`hasRootRole`) or the cache before its refresh. `doSerialize`
then runs the read, which may see entries the apply thread applied after the step (a put of a
protected key), and its re-check `ai.Revision != s.authStore.Revision()` sees `r` again and passes.
A JWT's revision is the token's, older than `r`, so it is refused (`ErrAuthOldRevision`).

## Proof

yes: the client's model checks a read's permission at the state it answers from (W0's `kvStep`);
here the check is at the state before the change and the answer after it. The auth store's specs
state the exact timing (`Spec/go_etcd_io/etcd/server/v3/auth/Api.lean`, `checkPost`: the views'
states; `Revision.spec`'s Changes); the request path (2c's `Range`, `Txn`, `RangeStream`) needs a fix
on the fork or a disjunct in `srvStep`, as for `nonissues/etcd-doserialize-auth-enable-race.md`
(decision for the user, `notes/specs-only/batch-3d.md`).

## Notes

A fix: bump the atomic after the batch transaction's `Unlock` (`commitRevision` writes the stored
revision under the lock, the atomic after), so that a reader seeing revision `r` sees the state of
`r`; or have `isOpPermitted` read the revision from the same read transaction as the user.
