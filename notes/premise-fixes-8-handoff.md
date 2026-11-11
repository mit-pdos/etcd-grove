# premise-fixes-8 (server half, S1/S2): handoff

Scope: `/shared/tmp/premise-fixes-8/scope.md` (approved D1-D4, "## Decisions"). This worktree does
S1 (request path gains `context.libCtxOk ctx`, no trust change) then S2 (the flip). Client half
(C1-C3) is in `/shared/etcd-grove-pf8c`; don't touch the client contracts.

## Done (S1, WIP commit)

- `EtcdServer.AuthInfoFromCtx.spec` + `context.libCtxOk ctx` (unused until S2), and its wrapper
  `EtcdServer.AuthInfoFromCtx.wpM` (ReqOn).
- Spec + proof pattern (`#Hlib` after the context's conjunct) via
  `/shared/tmp/premise-fixes-8/s1/addprem.py SPEC` (inserts after `mvcc.txnCtx ctx cd`/
  `context.isContext ctx cd`, adds the import, fixes the `wp_start` pattern):
  checkLease{Leases,Renew,TimeToLive}, checkMembershipOperationPermission, doSerialize,
  processInternalRaftRequestOnce, requireAuthInfo, raftRequest, v3rpc AuthAdmin.{isPermitted,
  requireAuthInfo}, authMaintenanceServer.{isPermitted,requireAuthInfo}, kvServer.Compact,
  EtcdServer.{LeaseLeases,LeaseRenew,LeaseTimeToLive,RemoveMember,Range,Txn,Compact,MemberList,
  LeaseGrant,LeaseRevoke,Authenticate,DeleteRange,Put}.
- ModeSpecs: `specOff` of processInternalRaftRequestOnce/raftRequest/doSerialize.
- AdminOn: `adminPreOn` + `libCtxOk` (covers every admin `specOn`).
- isWatchPermitted: spec unchanged, `libCtxOk ci` derived from `srvStreamIs`'s `grpcRunCtx`.
- Checked clean (lean-check): AuthInfoFromCtx, ReqOn, checkLease*, checkMembership..., AuthAdmin.*,
  doSerialize, processInternalRaftRequestOnce, raftRequest, isWatchPermitted, LeaseLeases,
  LeaseTimeToLive, RemoveMember, MemberList, kvServer.Compact, authMaintenanceServer.{isPermitted,
  requireAuthInfo}.

## Q1 decided (etcd-grove-81, under the user's delegation; questions.md, untracked by .gitignore)

`traceutil.Tracer.Start`'s post gains `□ (context.libCtxOk ctx -∗ context.libCtxOk ctx')` (done).
Go test `examples/premisefix/tracerctx` (gated, examples module; noop + SDK tracers): passes.
Forms accepted: isWatchPermitted unchanged; stronger posts of `EnsureTrace` and
`traceutil.wp_WithCancelBackground_noTrace` (both `libCtxOk`).

## Done after Q1

- `Tracer.Start` post, `EnsureTrace` post+proof, `wp_WithCancelBackground_noTrace` post+proof.
- Tactic `context_libKeys_ne [T.ty]` (LibKeys.lean): the side condition of
  `context.libCtxOk_of_valueWand` at a named key type (`WithValue(StartTimeKey)` etc.).
- Level-2 proofs: Put/Txn (`libCtxOk_of_valueWand` at StartTimeKey), DeleteRange, Range, Compact,
  LeaseGrant, LeaseRevoke, LeaseRenew, Authenticate, AuthnOn (`authnRaft_on`).
- Bundles: `srvCall` (+ `libCtxOk ci`; producers `ihave #Hlibc := libCtxOk_of_runCtx ci $$ Hrc` beside
  each `spanCtxOk_of_runCtx`), `lessorTTLOk`/`lessorLeasesOk` (InvLeaseRead), `raftLeaseRenew`
  (InvLeaseKeepAlive), `srvRevokeCtx` (RevokeCtx, from start's `#Hclib`); v3rpc
  `LeaseServer.{LeaseTimeToLive,LeaseLeases}` and `authMaintenanceServer.*` specs.

## Next, in order

1. The first full build after these (log `/shared/tmp/premise-fixes-8/s1/build1.log`): fix what it
   reports (expected: publishV3/monitorClusterVersions, auth-admin callers (AuthService,
   InvAuthAdmin), keep-alive, Results files, client served results, examples).
2. Go tests (Scope §4: S1 has only tracerctx; TestAuthInfoFromTLSReal is S2's).
3. Full build clean, `etc/tcb-report.py --check` (expect no change: Tracer.Start's text changes, not the
   axiom count; the collections `--check --update` only if the hash of trusted text is tracked),
   collections, `etc/gen-interface.py` for changed packages, `etc/gen-init.py --check`. STOP before land.sh.

## Build / check

`/shared/tmp/premise-fixes-8/s1/lc.sh FILE...` (lean-check, filtered; full output in
`/shared/tmp/premise-fixes-8/s1/lc.out`). Avoid running lean-check on many files whose shared
imports changed at once: concurrent Lake builds of one module gave spurious "Lean exited with code 1".
Targeted build: `systemd-run --scope -q -p MemoryMax=64G lake build --packages=/shared/tmp/manifest-ddc.json <mod>`.
