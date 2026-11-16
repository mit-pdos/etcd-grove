---
title: authSchemaSrv is false (lend grants writes; write-back budget; two encoding gaps)
found: 2026-11-12
by: S0 of the etcd_auth_safe Scope, axiom-skill review (report /shared/tmp/auth-safe/s0/report.md, Go tests /shared/tmp/auth-safe/s0/tests/)
blocks-proof: yes (for an auth closed theorem); no closed *_safe theorem rests on it
status: fixed and landed (auth-schema-fix, lean 51ee20f154, 2026-11-13; F3 e450457d89, F2 350380537e, F4 350baf65a5, F1 398c6dc09f + 10da96a817); etcd-grove-81's axiom re-review READY WITH CHANGES (unknown fields nil in the stored user and role messages, non-empty names, the per-batch put count recorded for D22), then its review's MAJ-1/MAJ-2 (nested unknown fields, `notes/auth-unknown-fields-nested.md`) fixed and re-reviewed GO; open follow-ups (a) `sizeCache` under `↦□`, (b) the client send's `wireLen` there. **Refuted again 2026-11-16** (the read contract's one-state snapshot, below): open, the fix to be decided (`notes/auth-schema-srv-scope.md`, Q1)
---
# `authSchemaSrv` is false

`authSchemaSrv` (`Proof/go_etcd_io/etcd/server/v3/etcdserver/AuthSrv.lean:81-106`), the trust-boundary
text of the auth store's schema and backend (D22's named premise of `server_new_auth_on`,
`authkv_startServer`, `authkv_Main`), is refuted four ways. Bugs in this repository's trusted text;
F3 and F4 are also etcd code facts unreachable from etcd's request path (nonissue candidates).

- **F2 (Go panic).** The lend `authBkLend` (`AuthBkHook.lean:70-74`) hands a tracked-bucket part
  (`rbPart`), which is write authority; a client writes garbage to `Auth`/`AuthUsers` through the
  backend's batch tx, and the read contract's reads then promise a recorded state while Go panics
  (`UnsafeReadAuthRevision` index out of range; `UnsafeGetUser` unmarshal `lg.Panic`). Fix: the lend a
  read-only bracket returning `authBucketsAt` of the snapshot's data.
- **F1 (ghost budget).** The text takes 2 write-back tokens yet promises unboundedly many write-backs
  (`CreateAuthBuckets`, batch `Unlock` = Unlock + Commit, `ForceCommit`); in the server's world
  (`srvWTStockInv`) the third write-back cannot restore `batchFree`'s `ver + n + k < 2^40`. Fix: charge
  `wbTok` per write as the off-mode `NewAuthStore.spec` does.
- **F3 (wrong result).** `GetAllRoles` ranges `[0x00, 0xff)` and misses a role named `"\xff"`, while
  `rolesOut` promises every role. Fix: bound `rolesOut` to names `< "\xff"`.
- **F4 (Go panic).** `UnsafePutUser` panics (`lg.Panic` on Marshal) on a role name that is not valid
  UTF-8 (proto3 string). Fix: a UTF-8 premise, with a law that `apply.irrDecode` yields valid UTF-8.

`etc/tcb-report.py` does not show it (a hypothesis). The axiom review is to be re-run on the revised text.

## Fixed (2026-11-12, branch auth-schema-fix)

- F3: `auth.rolesOut` lists only `roleListed` names (`n ≠ [] ∧ n < "\xff"`); RoleList's reply likewise.
- F2: `authBkLend` hands an abstract observation `RL` with a read-only law against the batch lock's
  `rbOwn` (no `rbPart`, so no write authority).
- F4: UnsafePutUser's clause takes the roles' `utf8Valid`; the store keeps `rolesUtf8` in the fuel's
  `authSmall`; the grant's role comes from a new trust-boundary law `apply.irrDecode_utf8` (Go test
  `/shared/tmp/auth-safe/fix-tests/irr_utf8_test.go`).
- F1: the write contracts take a write-back token parameter `Wb` (`Unlock` 2: schema's Unlock is the
  backend's Unlock then Commit; `ForceCommit` 1; `GetAllRoles` 2; `CreateAuthBuckets` 1), at the server
  `backend.wbTok d.γB`; `authSchemaSrv` drops its `ownToks d.γB.wb 2`. The tokens come from receipts:
  three per applied entry in the apply loop (`srvWTPool_take_extraOn`), and for the boot two from
  NewServer (`authKitIn`) beside the kit's two.
Trusted text old → new with Go evidence: `/shared/tmp/auth-safe/freeze-fix.md`.

## Second refutation (2026-11-16, the auth-schema-srv Scope): a read sees a half-applied step

`auth.authReadTxOk` (the read contract `authSchemaSrv`, `authSchemaSnap` and `authSchemaBoot` give,
through `authBackendOk`) promises each `RLock` one recorded state (`authSnap`; at a published lower
bound, `authSnapFrom`). Go's `batchTxBuffered.Unlock` writes a session's puts back into the read
buffer, releases `readTx`'s lock, and only then commits the delete it has pending, so a read
transaction in between sees the step's puts over bbolt's old snapshot: after `UserDelete(u)`, the new
revision with `u` still present, a state no step recorded. Go test (fails at the fork pin 6e8f0c004):
`nonissues/etcd-auth-readtx-delete-window-mixed-state/zz_authschema_window_test.go`
(`TestAuthSchemaReadWindowMixedState`, the auth store's real `UserAdd`/`UserDelete` and the read
calls of `CheckPassword`'s closure). The Go behavior is a nonissue (etcd's `Authenticate` re-reads the
user at apply): `nonissues/etcd-auth-readtx-delete-window-mixed-state.md`.

Consequences: `authSchemaSrv` is false, so `etcd_auth_safe`, `etcd_auth3_safe`, `etcd_authN_safe`
(which take it as `hD22`) are vacuous until it is restated; the proved
`auth.authStore.CheckPassword.spec` (`passwordChecked`: "the revision of a recorded state that has the
user") is false of Go too (proved over the false contract: it reads the user and the revision in one
transaction). The latest-state clause (a reader with the write token) is true. Per bucket the read is
one recorded state (no admin step deletes and puts in the same auth bucket), which is what the fix
options build on: `notes/auth-schema-srv-scope.md`, §2 and Q1.

### The fix (A0, 2026-11-16, branch auth-schema-srv; Q1 (a), approved by the user via etcd-grove-02)

The read contract gives a view, a state per bucket (`auth.BkView`: the `auth` bucket's, `authUsers`',
`authRoles`'), each recorded at an index at least the reader's lower bound, the users' index not above the
`auth` bucket's (`auth.authViewSnap(From)`, `Buckets.lean`); each read is at its bucket's state
(`authReaderOkV`). The latest clause (with the write token) keeps one state. `passwordChecked`: the user in a
recorded state, the revision of a not-earlier one. Per bucket the view is recorded only if no batch session puts
and deletes in one bucket (`TestAuthSchemaReadMixedBucketSession` fails otherwise), so the write contract
`authBatchTxLk(R)` gains a session token `Sw : AuthSess → IProp` (`Lock` gives `Sw AuthSess.init`; a put into
the users' or roles' bucket needs no delete there in the session, a delete no put; `Unlock` takes it). The
store's admin steps meet it. Go: `TestAuthSchemaReadPerBucket` (the store's steps, 0 per-bucket violations,
the old text's control fails ~15k times a run). Ledger: `notes/specs-only/ledger.md`, 2026-11-16.
