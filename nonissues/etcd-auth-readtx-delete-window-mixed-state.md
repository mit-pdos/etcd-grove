---
upstream: none
checked: 2026-11-16
links:
  - etcd-io/etcd#17119 pr merged: related, not this behavior (the commit at `Unlock` when a delete is pending, which leaves the window below)
blocks-proof: yes
---

# auth: a read of the auth buckets can see an admin change half applied (its puts, not its deletes)

An auth read transaction (`lockedReadTx`, `GetUser`, `GetAllUsers`) that starts while the apply
thread finishes `UserDelete` (or `RoleDelete`) sees the step's puts but not its deletes: the new auth
revision with the deleted user still present. `authStore.CheckPassword` reads the user and the
revision in one such transaction, so it can check a just-deleted user's password and return the
revision of the step that deleted it.

**Why not an issue:** no wrong result in etcd: `CheckPassword` is the only reader of two keys, and the
`Authenticate` it serves re-reads the user when the request is applied (`authStore.Authenticate`,
`GetUser`), after the delete is committed, and fails; a single-key read sees the key as before or
after the step. The test (`etcd-auth-readtx-delete-window-mixed-state/`, copied into `server/storage/schema`
at the fork pin 6e8f0c004, go1.27.3) shows the half-applied state at the schema read transaction:

```
$ go test ./storage/schema/ -run TestAuthSchemaReadWindowMixedState -count=1 -v
    zz_authschema_window_test.go:84: reads 140, reads of an unrecorded state 4 (first at revision 3)
--- FAIL: TestAuthSchemaReadWindowMixedState (0.02s)
```

**How:** `batchTxBuffered.Unlock` (`server/storage/backend/batch_tx.go:328-357`) writes the session's
puts back into the read buffer under `readTx.Lock()`, releases it, and only then commits the bbolt
transaction because a delete is pending (`commit` takes `readTx.Lock()` again). A read transaction
that takes `readTx.RLock()` in between reads the read buffer (the new revision) over bbolt's old
committed snapshot (the deleted user, which `UnsafeDelete` removed only from the uncommitted bbolt
transaction).

## Proof

yes: the trusted read contract `auth.authReadTxOk` that `authSchemaSrv` (and `authSchemaSnap`,
`authSchemaBoot`) gives, a named hypothesis of `etcd_auth_safe`, `etcd_auth3_safe` and
`etcd_authN_safe`, promises every `RLock` (plain and at a published lower bound) one recorded auth
state; this read is in none. The hypothesis is false, so those theorems are vacuous until it is
restated (`notes/auth-schema-srv-refuted.md`, "Second refutation"; `notes/auth-schema-srv-scope.md`).
The latest-state clause (a reader holding the write token) is true: no auth batch is open.

## Notes

A fix in etcd (not needed by etcd): keep `readTx` locked from the write-back through the commit when a
delete is pending. Per bucket the read is consistent: no admin step both deletes and puts in one
auth bucket, so each bucket's contents are those of the step's state before or after.
