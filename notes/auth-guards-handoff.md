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
- **G2** (except `isWatchPermitted`): `specC`/`wp_proofC` of `EtcdServer.requireAuthInfo`,
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

## Follow-ups

- (D22, decided by etcd-grove-81 2026-11-14) With auth off the admin guards' error may be `AuthInfoFromCtx`'s,
  which `isReqAuth` (of `NewAuthStore`'s axiom) leaves free, so `adminWhy .off` is `True`. Discharging
  `NewAuthStore`'s axiom by proof (D22) would give "no error with auth off" without new trust.
- `isWatchPermitted` (after k8s 7f-3b), `served_of_frozen` for `permWhy` (G4).
- The reason-free guard specs other than `EtcdServer.requireAuthInfo.spec` (kept for the lease entry points,
  D5) have no caller left; delete them after review.

## Pitfalls

- `cases h : E.authMode.isOn` rewrites the goal; use `rcases (Bool.eq_false_or_eq_true E.authMode.isOn).symm with hon | hon`.
- A pure goal after `iapply` of a `∀ _ : P, Q` hypothesis is a Lean goal: `exact`, not `ipureintro`.
- `auth.authErrOf e` names `e.var`: `simp only [auth.AuthErr.var]` before framing the variable's `↦□`.

## Build

`lake build --packages=/shared/tmp/manifest-ddc.json <targets>` under `systemd-run --scope -q -p MemoryMax=64G`;
`etc/lean-check.py` with `LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json`. `InvRequest.lean` changed:
its importers rebuild (fast with the module system: ~2 s each).
