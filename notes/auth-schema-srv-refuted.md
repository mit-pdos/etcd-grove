---
title: authSchemaSrv is false (lend grants writes; write-back budget; two encoding gaps)
found: 2026-11-12
by: S0 of the etcd_auth_safe Scope, axiom-skill review (report /shared/tmp/auth-safe/s0/report.md, Go tests /shared/tmp/auth-safe/s0/tests/)
blocks-proof: yes (for an auth closed theorem); no closed *_safe theorem rests on it
status: open; fixes decided by etcd-grove-81 (stage auth-schema-fix, before etcd_auth_safe)
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
