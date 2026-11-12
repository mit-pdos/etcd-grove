# auth-schema-fix: handoff (2026-11-12)

Stage of etcd-grove-81: make the auth results non-vacuous (S1: remove `auth.ValidSpec`; S0's F1-F4
in `authSchemaSrv`). Worktree `/shared/etcd-grove-authfix`, branch `auth-schema-fix` (from lean
`2f8cf80b7e`). Plan: `/shared/tmp/auth-safe/fix-plan.md`; Freeze package (in progress):
`/shared/tmp/auth-safe/freeze-fix.md`. Not landed; STOP for 81's axiom re-review once the targeted
builds pass.

## Done (committed, targeted builds pass)

- F3 (`e450457d89`): `auth.roleListed n := n ≠ [] ∧ GoStringLt n [0xff]`; `rolesOut` and
  `roleListOut` (RoleList's reply) list only those roles. nonissues F3 and F4 written.
- F2 (`350380537e`): `authBkLend` hands an abstract observation `RL` with the law
  `□ ∀ r, RL -∗ backend.rbOwn d.γB r -∗ ⌜authBucketsAt st r⌝ ∗ RL ∗ backend.rbOwn d.γB r`
  (no `rbPart`: no write authority); `bkLendW` the same shape; `srvAuthApplyResB_lend`,
  `acRes_lend`, `bkLendW_none`, the window (SnapSendBranch: the law applied inside the
  snapshot's observation, then `snapObsA` at no lent bucket) adapted. Built: SnapSendBranch,
  StoreLatest, AuthComp, AuthSrv, SnapAuthRecover, ApplyAllSnap.
- Go evidence for F4's supply: `/shared/tmp/auth-safe/fix-tests/irr_utf8_test.go` (passes at the
  server pin: `pbutil.MustUnmarshalMessage` panics on an InternalRaftRequest whose UserGrantRole
  role/user, UserAdd name or RoleAdd name is not valid UTF-8).

## S1 (partly committed; STOPPED at blocker 2, reported to etcd-grove-81 2026-11-12)

Committed (targeted build passes: TokenKeeperRun, authStore__AuthInfoFromCtx/authInfoFromToken,
AuthReqDerive): the token contract's `info` clause takes the hlc-generic `auth.ctxDoneRecv ci`
(`auth/CtxDone.lean`, with `auth.anyRecv` moved there from TokenSimple, and the law
`auth.ctxDoneRecv_of_ctxDoneAny` at hasLC); `tokenSimple_isValid` over it (nil Done:
`chan.wp_select_blocking_nil` + `chan.nilClausePre_recv`); `ValidSpec`, `tokenSimple_info`,
`tokenProviderOkCtx`, `tokenSimple_okCtx` deleted; `tokenSimple_okA(_run)` take `simpleWaitOk p`;
the store specs `authInfoFromToken`/`AuthInfoFromCtx` take `ctxDoneRecv`; AuthReqDerive converts
isReqAuth's `ctxDoneAny`. Results' `token_simple_ok` now states `tokenProviderOkA`.

**Not building yet**: `etcdserver/AuthSrv.lean` (`authSrvTP_on` still takes `hValid :
auth.ValidSpec`) and its users in `etcdserver/Results.lean` (`srv_auth_tp_on`, `server_new_auth_on`)
and `examples/etcd/auth/Results.lean`. Blocker 2: 81's route (authSrvTP's pre carries the waiter
contract, NewServer discharges it) fails: the waiter closure reads `srv.applyWait`, which Go sets
only in `start` (server.go:568), so at NewServer the field is nil and the closure panics if called.
Waiting for 81's decision (questions.md).

## Next, in order

1. S1: blocker 2 per 81's answer; then AuthSrv `authSrvTP_on` drops `hValid`, etcdserver Results
   `srv_auth_tp_on`/`server_new_auth_on`, authkv Results (exported: CP).
2. F4 (plan step 4): UnsafePutUser `∀ x ∈ ur.roles, utf8Valid x` in authBatchTxLkR and
   authBatchTxLk; state invariant `rolesUtf8` beside permKeysOk; `apply.irrDecode_utf8` (new
   trust-boundary law, Go test above).
3. F1 (plan step 5, decided by 81: see questions.md): `Wb` parameter, boot's extra 2 tokens from
   the server's write-back pool via receipts.
4. Notes (`notes/auth-validspec-false.md`, `notes/auth-schema-srv-refuted.md` status, decisions.md
   entry, STATUS.md), interfaces (`etc/gen-interface.py etc/api/<pkg>.txt`), tcb collections,
   Freeze package complete; STOP.

## Pitfalls

- InvAuth's write/read contracts sit in hlc-generic sections in places; check the section before
  using hasLC-only vocabulary.
- `rbPart_none` takes the map explicitly: `backend.rbPart_none d.γB ∅`.
- Build: `export TMPDIR=/shared/tmp; systemd-run --scope -q -p MemoryMax=64G lake build
  --packages=/shared/tmp/manifest-ddc.json <modules>`; full build under flock with etc/timed-build.py.
