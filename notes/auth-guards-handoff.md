# auth-guards handoff (auth-guard-completeness G0-G3)

Worktree `/shared/etcd-grove-auth3`, branch `auth-guards` (off lean `edc79e0ba7`, the Scope merged in).
Scope: `notes/auth-guard-scope.md`; decisions: `questions.md`, section "auth-guards".

## Done

- **G0** `Proof/go_etcd_io/etcd/server/v3/etcdserver/AuthWhy.lean`: `reqSideWhy`, `authedWhy`, `adminWhy`,
  `permWhy`, `authedOutC`, `adminOutC`, the drop lemmas, `authErrOf_apart` (two auth error variables of
  different messages differ), `authedWhy_not_permissionDenied`, the guards' helper lemmas.
  The store-side vocabulary: `Proof/go_etcd_io/etcd/server/v3/auth/WhyDefs.lean` (`noPrincipalFrom`,
  `tokRefusedFrom`, `adminRefusedFrom`, `adminErrOf`, `adminVerdictFromO`).
- **G1** `auth/FreshCtx.lean` (`AuthInfoFromCtx.specLb`, `wp_lb`), `auth/FreshAdmin.lean`
  (`IsAdminPermitted.specLbO`, `wp_lbO`; `wp_lb` derived), `isReqAuthBound`'s two new rows
  (`InvRequest.lean`) and their producer (`isReqAuthBound_of_authInv`, `AuthReqDerive.lean`; threaded through
  `srvAuthBound_of_authInv`, `authStoreKit_on`, `authSrvTP_on`, `Results.lean`'s `auth_ctx_lb`,
  `auth_admin_permitted_lbO`), `isReqAuth_ctxMLb`, the server's `EtcdServer.AuthInfoFromCtx.specLb`/`wp_proofLb`.
- **G2** (`isWatchPermitted`: its own section below): `specC`/`wp_proofC` of `EtcdServer.requireAuthInfo`,
  `EtcdServer.checkMembershipOperationPermission`, `v3rpc.AuthAdmin.{isPermitted,requireAuthInfo}`,
  `v3rpc.authMaintenanceServer.{isPermitted,requireAuthInfo}`; linked (`etc/link-lean-first-{server,v3rpc}.txt`,
  `<fn>+C`, `EtcdServer__AuthInfoFromCtx+Lb`).

## G2 revision (2026-11-14, etcd-grove-81's review)

Every reason needs a flag read `true` no older than `n`; errors tied to their cases
(`auth.adminRefusalFrom`); `specC` the one proved spec of each guard, `spec` its corollary at `n = 0`
(`authPubLbM_zero`, now in `auth/WhyDefs.lean`); `isReqAuthBound`'s rows read through accessors
(`isReqAuthBound_{enLb,ctxLb,adminLb}`, `isAuthEnabled_ctxMLb`); `authed_served_of_frozen`,
`admin_served_of_frozen` (`auth.authFrozenFrom`); Go tests `notes/auth-guard-scope/zz_guard_why_test.go`.

## G3 (2026-11-14)

- `readErrIs_authErrVarIs` (`AuthWhy.lean`): the read path's errors are not auth error variables (message
  cells; `DeadlineExceeded` by its type). The raft request's errors need no such check: every guarded
  wrapper's guard branch is told apart by `Pin` (`guardOutC`, `guardOut1C`, `compactOutC`), and
  `RemoveMember`'s by its own disjunct.
- In place (one spec each, no caller in a proof but `etcd_compactHandlerOk`'s, which now takes `na = 0`):
  `EtcdServer.{MemberList,RemoveMember}`, `v3rpc.kvServer.Compact`,
  `v3rpc.authMaintenanceServer.{Defragment,Hash,HashKV,MoveLeader,Downgrade,Snapshot,Status,Alarm}`: a bound
  `n`, `□ auth.authPubLbM E.authMode n` (the admin ones drop `srvAdminNilOk`), the guard's branch with its
  reason; over the guards' `specC`. `v3rpc.togRPCError_out` keeps `grpcErrOut`.
- `n` = the auth state the request saw: see the G3 report (the entry points take any `n`; the request
  path above them, gRPC handlers and the client model, carries none, as for `Range`).

## G3 re-check fixes (etcd-grove-81, 2026-11-14)

- B: `permWhy` ties `ErrAuthOldRevision` (non-zero revision) and `ErrPermissionDenied` (non-zero, current
  revision, user-part refusal) to their cases.
- C: `auth.authFrozenFrom` replaced by `auth.histFrozenFrom` over the authority's history and
  `auth.authOwn_frozen`; `*_served_of_frozen` take and give back `auth.authOwn`. `admin_served_of_frozen`'s
  docstring names its TLS vacuity.
- A: naming fixed (disable race for `requireAuthInfo`, enable race for the admin check). The order
  `n ≤ i ≤ j` for the authenticated class is not done: the store's freshness (`revFresh`) gives a flag
  read as some state's at an index at least the published one, not ordered with a later read's.

## isWatchPermitted (2026-11-14; branch `auth-guards-watch`, on lean `008b848fbe`)

- The store's refusal half, each error tied to its case: `auth.permRefusalFrom`/`permRefusalM`,
  `isOpPermitted.specLbR`, `IsRangePermitted.specLbR` (`auth/FreshCheck.lean`, `auth/FreshWrap.lean`).
- `apply.isAuthStoreRangeLbR` (`apply/AuthCheckTxnLb.lean`), a third row of `authStoreLbM`
  (`StoreLatest.lean`), produced by `authStoreKit_on` (`AuthSrv.lean`), the only builder of `srvAuthLb`.
  The exported results whose premises hold `srvAuthLb` now ask for this row too with auth on (listed in
  STATUS's entry); `authStoreKit_on` supplies it.
- `v3rpc.serverWatchStream.isWatchPermitted.spec`: on an error, `∃ info, permWhy … err info k e .read`
  (`AuthWhy.lean`'s `permWhy`, now over `auth.permRefusalFrom`; `permWhy_of_reqSide`, `permWhy_anon`,
  `permWhy_bound`, `permWhy_off`). `recvLoop` drops the reason.
- The anonymous principal's `ErrUserEmpty` beside `noPrincipalFrom`'s flag read `false` is a race with
  `AuthEnable` (`AuthInfoFromCtx` reads `false`, `isOpPermitted` `true`): added to
  `nonissues/etcd-admin-check-authenable-race.md`.
- Independent review (2026-11-14): PASS, no blocker or major; the four minor findings (the race, the
  results' premises, these notes, stale docstrings) fixed in docs and records only.

## G4 (2026-11-14; branch `auth-guards-g4`, on lean `e521c084f6`): the serializable read path and apply

- `doSerialize` (`Spec/.../EtcdServer__doSerialize.lean`): new premises `srvAuthLb s E ∗ □ authPubLbM E.authMode n`
  (its only callers, `Range`/`Txn`, hold them; `specOff` supplies them at `n = 0`), `chk`'s contract gains a
  refusal predicate `R` (`∀ _ : err ≠ nil, R info err`), the error branch `serialWhy` (`AuthWhy.lean`): the
  request side's reasons, `chk`'s refusal of the auth info the request side gave (`infoWhy`), or the revision
  re-check (`oldRevWhy`: a state no older than `n` whose revision is not the info's, the info bound, with the
  flag read `true` or from the TLS fallback, `nonissues/etcd-auth-old-revision-auth-disabled.md`).
- For `oldRevWhy`'s flag read: the store's and server's `AuthInfoFromCtx.specLb` give, for a non-`nil`
  principal, the flag read `true` at a state no older than `n` (server: or `srvTLSId`); `isReqAuthBound`'s
  third row carries it; `EtcdServer.AuthInfoFromCtx.wpMLb` (`ReqOn.lean`); `srvAuthLb_revision` (`ReadOn.lean`:
  `Revision()` at the bound, from the lease row of `authStoreLbM`, read only).
- `ReadWhy.lean`: `rangeWhy`/`txnWhy` (reasons in `Range`'s/`Txn`'s terms), `rangeWhyOut`/`txnWhyOut` (a refusal
  with its reason, or the read index's error, or the read's own), lemmas from `serialWhy`, ctx transport.
  Not `authErrVarIs err -∗ why` (G3's form): the read's own errors include a `%w`-wrapped context error, opaque
  in Perennial's errorf model, so it cannot be told apart from an auth variable.
- `Range.spec`, `Txn.spec` (exported): error branch `∗ rangeWhyOut …`/`∗ txnWhyOut …` (pure strengthenings).
- `apply/AuthCheckTxnLb.lean`: the read-only txn's checks over a generic refusal predicate `W`
  (`permCheck3LbW`, `isAuthStoreRangeLbW`, `checkTxnReqs_lbW`, `checkTxnPermission.specLbW`/`wp_lbW`,
  `CheckTxnAuth.specLbW`/`wp_lbW`/`wp_lbW_linked`); `checkTxnPermission.wp_lb` now derived (`W := True`); the
  exported `apply_check_txn_auth_lb` unchanged. `Txn` takes `specLbW` (link: `=apply.CheckTxnAuth.wp_lbW_linked`).
- `apply/Results.lean`: `admin_rejected_why` (`adminRejL` ⇒ `adminRefused` at the latest state),
  `kv_rejected_why`/`kv_rejected_why_quota` (`authOutL` with `.rejected .auth` ⇒ `refusedL`).
- `rangeWhy_of_authErr` (`ReadWhy.lean`, review minor 7): an auth error variable in `rangeWhyOut` is
  `rangeWhy`, or `rangeKeys`' wrapped context error (opaque: `errDesc` has no law for auth variables).
- Review (etcd-grove-81, 2026-11-14): (a)-(c) accepted; (d) accepted for KV only.

### Left (G4)

- **The admin rejection's reason does not reach the proposer** (review MAJOR (d)). `admin_rejected_why` is
  apply-level only: `admin_state_of_latest` (`Results.lean`) gives `adminStateR rq st st`, which a failing
  step also gives, and `adminTieAr` (`KVAuthModel.lean`) says nothing when the result's error is set (nor
  for a rejected outcome). Fix: in `adminTieAr`, `out = .rejected` (or `v.Err' ≠ nil`) ⇒ `adminRefused` at
  `st` ∨ the step's own error, produced by `adminOut_model` (`ApplyTieOn.lean`) from `adminRejL` and carried
  to the waiter; or an etcdserver-level result. Not done: `adminTieAr` is in the waiter's and the request
  path's exported specs (21 uses), beyond the guards' internal specs.

## Follow-ups

- (G3 review, etcd-grove-81 2026-11-14; needed for G7) The reason does not reach the gRPC error: `grpcErrMapOk`
  pins only mvcc's two read errors in `toGRPCErrorMap`, so a caller holding the converted error learns nothing
  of the guard's `e0`. Add the auth errors' entries (as `util.go` has them) to `grpcErrMapOk`.

- (D22, decided by etcd-grove-81 2026-11-14) With auth off the admin guards' error may be `AuthInfoFromCtx`'s,
  which `isReqAuth` (of `NewAuthStore`'s axiom) leaves free, so `adminWhy .off` is `True`, and so is
  `permWhy .off` (the watch's `isWatchPermitted` calls `AuthInfoFromCtx` too). Discharging
  `NewAuthStore`'s axiom by proof (D22) would give "no error with auth off" without new trust.
- `served_of_frozen` for `permWhy` (G4).
- (decided by etcd-grove-81 2026-11-14) The ordered flag race: a store freshness invariant that follows the
  flag's latest index (`revFresh` gives only some state at an index at least the published one), so that
  `authedWhy` can require the `true` read at `i` and the `false` read at `j` with `n ≤ i ≤ j`.
- Done 2026-11-14: the reason-free guard specs without callers are deleted; each guard has one spec (with
  reasons), but `EtcdServer.requireAuthInfo`, whose reason-free `spec` the lease entry points take (D5),
  beside its `specC`.

## Pitfalls

- `cases h : E.authMode.isOn` rewrites the goal; use `rcases (Bool.eq_false_or_eq_true E.authMode.isOn).symm with hon | hon`.
- A pure goal after `iapply` of a `∀ _ : P, Q` hypothesis is a Lean goal: `exact`, not `ipureintro`.
- `auth.authErrOf e` names `e.var`: `simp only [auth.AuthErr.var]` before framing the variable's `↦□`.

## Build

`lake build --packages=/shared/tmp/manifest-ddc.json <targets>` under `systemd-run --scope -q -p MemoryMax=64G`;
`etc/lean-check.py` with `LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json`. `InvRequest.lean` changed:
its importers rebuild (fast with the module system: ~2 s each).
