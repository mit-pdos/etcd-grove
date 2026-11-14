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

## Next, in order

1. G2 hard stop: report the six `specC`s (git diff of `Spec/`) to etcd-grove-81 for review.
2. `isWatchPermitted` (after k8s 7f-3b lands, Scope §6): a pure strengthening with `permWhy`.
3. G3: the guarded entry points (Scope §2.4) over the `specC`s: `MemberList`, `RemoveMember`, `kvServer.Compact`,
   `ams.{Defragment,Hash,HashKV,MoveLeader,Downgrade,Snapshot,Status,Alarm}`; `guardOutC`. Check first that
   `LinearizableReadNotify`'s and `raftRequest`'s errors are not auth error variables (G0's checks).
4. G0's `served_of_frozen` (not needed by G1-G3; groundwork for G7).

## Pitfalls

- `cases h : E.authMode.isOn` rewrites the goal; use `rcases (Bool.eq_false_or_eq_true E.authMode.isOn).symm with hon | hon`.
- A pure goal after `iapply` of a `∀ _ : P, Q` hypothesis is a Lean goal: `exact`, not `ipureintro`.
- `auth.authErrOf e` names `e.var`: `simp only [auth.AuthErr.var]` before framing the variable's `↦□`.

## Build

`lake build --packages=/shared/tmp/manifest-ddc.json <targets>` under `systemd-run --scope -q -p MemoryMax=64G`;
`etc/lean-check.py` with `LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json`. `InvRequest.lean` changed:
its importers rebuild (fast with the module system: ~2 s each).
