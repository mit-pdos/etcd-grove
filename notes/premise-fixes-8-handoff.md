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

## Also done (builds 1-4)

- v3compactor: `compactableOk` (+ `libCtxOk ctx` after `spanCtxOk`), the `isPeriodic`/`isRevision`
  state (+ `libCtxOk ctx`; their `Persistent` instances need `synthInstance.maxSize 1024`),
  newPeriodic/newRevision (`#Hclib` from `wp_WithCancelBackground_noTrace`), every `icases`
  pattern `#Hspc, #Hclib, #Hcancelf`; CompactEnv's `compactableOk_server_mode`.
- `EtcdServer.start`: `#Hclib` into `srvRevokeCtx_intro`'s frame.
- `LeaseServer.leaseKeepAlive`: `ihave #Hlibk := libCtxOk_of_runCtx ci $$ Hrunctx`.
- **Exported results whose text changed** (list at the S1 checkpoint, Scope S.6):
  `Proof/go_etcd_io/etcd/server/v3/etcdserver/Results.lean`'s `range_linearizable`,
  `range_serializable`, `txn_readonly`, `txn_applied` (pre + `context.libCtxOk ctx`).
- Full build 4 (`/shared/tmp/premise-fixes-8/s1/build4.log`, commit 9c85382de4): the only failure is
  `Proof/go_etcd_io/etcd/client/v3/LeaseReadServed.lean:100` and `:178` (unsolved goals: the
  `lessorTTLOk`/`lessorLeasesOk` contracts now take `context.libCtxOk ci`; supply it from the run
  context, `libCtxOk_of_runCtx`, as elsewhere). Lake stops the modules importing it, so expect more
  past it (client served results, `examples/lib/etcdstart/ServedLease`, auth-admin callers via
  `AuthService`/`InvAuthAdmin`, publishV3/monitorClusterVersions if they reach raftRequest).

## Next, in order

1. Fix LeaseReadServed; full build again (flock, 64G); repeat until clean. Producers: request
   contexts `libCtxOk_of_runCtx ci $$ Hrc` (beside each `spanCtxOk_of_runCtx`); `WithValue` at a
   server key: `context.libCtxOk_of_valueWand ... (by context_libKeys_ne [K.ty]) $$ Hdel Hlib`;
   `WithCancel/WithTimeout(Background())`: `context.libCtxOk_bgFrom`; `TODO()`: `libCtxOk_todo`.
   For a chained `WithTimeout(s.ctx)` the Scope's new law `libCtxOk_from` (ctxValueFrom parent child
   with parent nil at the keys) may be needed (not written yet).
2. Then: `etc/tcb-report.py --check` (expect no axiom/sorry change), collections, interfaces
   (`etc/gen-interface.py etc/api/<pkg>.txt` for changed packages, incl. raft? no; server/v3rpc,
   traceutil, client), `etc/gen-init.py --check`; commit; STOP before land.sh with the report
   (list the four Results above, and any further exported text change).
3. S2 after S1 lands (Scope S.2; D2), with the old → new text STOP first.

## Pitfalls

- Don't run lean-check on several files whose shared imports changed: parallel Lake builds of one
  module fail spuriously ("Lean exited with code 1"); a plain `lake build <mod>` then passes.
- `git commit -a` needs the `-c user.name=... -c user.email=...` flags (no identity configured).
- `questions.md` is gitignored (untracked, in the worktree): Q1 and the accepted forms are there.
- Monitor/grep on the build log: match `^error: build failed|^Some required targets`, not
  "Terminated" (k8s type names contain it).

## Build / check

`/shared/tmp/premise-fixes-8/s1/lc.sh FILE...` (lean-check, filtered; full output in
`/shared/tmp/premise-fixes-8/s1/lc.out`). Avoid running lean-check on many files whose shared
imports changed at once: concurrent Lake builds of one module gave spurious "Lean exited with code 1".
Targeted build: `systemd-run --scope -q -p MemoryMax=64G lake build --packages=/shared/tmp/manifest-ddc.json <mod>`.
