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

## BLOCKED (STOP reported to etcd-grove-81)

`traceutil.Tracer.Start` (an axiom, `Spec/go_etcd_io/etcd/pkg/v3/traceutil/Tracer__Start.lean`)
returns the context the request path then passes (after `WithValue(StartTimeKey)`) to
`raftRequest`/`doSerialize`/`AuthInfoFromCtx`. Its post carries `spanCtxOk`/`startTimeOk`
preservation but nothing for `libCtxOk`, so Put, DeleteRange, Txn, Range, Compact, LeaseGrant,
LeaseRevoke, LeaseRenew cannot discharge the new premise. Proposed trusted change:
post `+ □ (context.libCtxOk ctx -∗ context.libCtxOk ctx')`.

## Next, in order (after the decision)

1. Tracer.Start post (if approved) + extend `examples/sweeprepairs/tracer` (Value at grpc's keys
   delegates; the span key answers an otel span or ctx's).
2. Finish the level-2 proofs (Put, DeleteRange, Txn, Range, Compact, LeaseGrant, LeaseRevoke,
   LeaseRenew (WithTimeout: law `libCtxOk_from`), Authenticate, AuthnOn).
   `EnsureTrace` (proved) may need a stronger post (`libCtxOk` through `WithValue(TraceKey)`).
3. Upward: v3rpc bundles (`srvCall`, InvLease, InvLeaseRead, AuthService, InvAuthAdmin, InvWatch*),
   auth-admin methods' callers, revokeExpiredLeases/RevokeCtx, publishV3, monitorClusterVersions
   (`traceutil.wp_WithCancelBackground_noTrace`: strengthen its post with `libCtxOk`),
   LeaseCheck, NoRefusal, apply/Contracts, Results, client served results, examples.
4. Go tests (Scope §4), full build (flock, 64G), tcb --check, collections, interfaces, gen-init.

## Build / check

`/shared/tmp/premise-fixes-8/s1/lc.sh FILE...` (lean-check, filtered; full output in
`/shared/tmp/premise-fixes-8/s1/lc.out`). Avoid running lean-check on many files whose shared
imports changed at once: concurrent Lake builds of one module gave spurious "Lean exited with code 1".
Targeted build: `systemd-run --scope -q -p MemoryMax=64G lake build --packages=/shared/tmp/manifest-ddc.json <mod>`.
