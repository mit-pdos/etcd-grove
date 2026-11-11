# premise-fixes-7: handoff

Scope: `/shared/tmp/premise-fixes-7/scope.md` (approved, D1-D5; this stage = item 3 (Part C),
item 2 (Part B), item 1 client/k8s side (Part A without FromIncomingContext, AuthInfoFromTLS,
isReqAuth*, Invoke/NewStream), the perRPCCredential docstring fix).

## Done

- Go tests (f01a12f713): `examples/premisefix/ctxvalue` (examples module) and
  `examples/premisefix/k8sctx` (own go.mod, k8s pins of `examples/k8s/etcd3`). All pass.
  `examples/go.mod` gained direct requires (grpc-prometheus provider, otelgrpc, otel sdk/trace).
- Item 3 (4e8fddea73): `Changer.apply` (both trees) without `ConfChangeType.String`; links
  regenerated; the four axiom files and their two interface files deleted; `Results.lean`'s
  `#print axioms raftpb.ConfChangeType.wp_String` dropped. Targeted build of both raft
  `Results` clean. `tcb-baseline` not yet updated (checkpoint (b): `--check --update`, -1 axiom).
- Item 2 (uncommitted at the time of writing, see below): `InvGrpcStream.lean` (srvRawStreamIs /
  srvStreamIs Recv error `statusErrOk`; `srvStreamInterceptorOk`, `grpcStreamHandlerOk`,
  `grpcStreamMethodOk(R)` with `srvErrOk`; `srvStreamChainWP_of_ok` restated);
  `newStreamInterceptor` proof; `_Watch_Watch_Handler` spec/proof (post `srvErrOk`); `recvLoop`
  spec/proof (post `streamErr ∗ statusErrOk`); `Watch` spec/proof (post `srvErrOk`; the context
  error through `applyErrIs_of_isCtxErr`/`applyErrIs_srvErrOk`, importing `InvRead`); v3rpc
  `Results.lean` (`watch_streamHandlerOk`, `etcd_watchMethodOk`).

- Q1 (de89ac4e2b, decided by etcd-grove-81): `ErrGRPCWatchCanceled_init`'s post gains
  `statusErrOk` (gen-init.py `_RWERRS`); `rpctypesInit` and `watchPkgVars` (new
  `v3rpc.statusMsgErrVar`) carry it; `Watch`'s placeholder `sorry` gone. Item 2's leaves built
  clean (v3rpc and cache `Results`, the served examples).
- Item 1, client and k8s part (uncommitted at the time of writing, then committed with this
  handoff): vocabulary `Proof/context/LibKeys.lean` (`context.valueAt`, the opaque
  `metadata.transportMD`/`builtRawMD`, `peer.transportPeer`, `trace.otelSpan`, `incomingCtxOk`,
  `outgoingCtxOk`, `peerCtxOk`, `spanValOk`, `spanValOkNil`, `libCtxOk`, laws `_of_nil`,
  `_of_ctxValueNil`, `_background`, `_todo`, `_bgFrom`, `_of_valueWand`) and
  `Proof/k8s_io/apiserver/pkg/audit/CtxKeys.lean` (`utiltrace.builtTrace`, `k8sCtxOk`,
  `k8sctx.spanCtx`, laws); `channelContext.Value` spec+proof (returns nil) and
  `chanCtx_valueNil`/`chanCtx_libCtxOk` (ChanCtx.lean; not linked yet, for pf8);
  restated: `grpcRunCtx` (+ `libCtxOk`), `logUnaryRequestStats` (`ctx : GoInterfaceOk`,
  `peerCtxOk`), `AppendToOutgoingContext` (pre/post `outgoingCtxOk`), `WithRequireLeader` (inner
  post `libCtxOk ctx'`), `WithTimeoutBackgroundMd` (post `libCtxOk ctx'`), `GetAuditIDTruncated`
  (`GoInterfaceOk`, `valueAt auditKey`), k8s `tracing.SpanFromContext` (`GoInterfaceOk`,
  `spanValOk`, trace key), `tracing.Start` (pre/post `k8sCtxOk`), `HistogramVec.WithContext`
  (pre `spanValOkNil ctx`: nil allowed, as Go); perRPCCredential docstring and
  `notes/axiom-review/ctxok-done.md` corrected. Callers: store.{Get,Create,GetList,
  GuaranteedUpdate} (+ `k8sCtxOk ci`), the cacher chain (+ `k8sctx.spanCtx ctx` /
  `spanValOkNil ctx`), `newLogUnaryInterceptor`, auth example (`reqCtx`, `Work`, `SetUp`),
  `TimeoutCtx`, `NewLeaseFromLeaseClient`, k8s `call.lean` (`k8sCtxOk_background`).

- Checkpoint data (after b95a5598b9): full build clean (flock, 64G); `tcb --check`: only
  `raftpb.ConfChangeType.String.wp_proof` gone (baseline and 21 collections updated); gen-init
  `--check` and errdesc-check ok; interfaces: only raft's `Changer__apply.txt` (item 3)
  regenerated. Go tests `premisefix/{ctxvalue,k8sctx}` pass.

## STOP (waiting for etcd-grove-81): D5 and FromOutgoingContext ripple

`watchCtx` gaining `outgoingCtxOk` (D5) forces it into the client's watch contracts
`isEtcdWatcher` (cache) and `isEtcdRangeWatcher` (concurrency Mutex/Election, leasing, recipes,
server v3lock/v3election via NewSession), whose users then need it of their contexts; and
`FromOutgoingContext`'s premise forces it into `kaCtxOk`/`lessor.KeepAlive`/`isEtcdLease`
(exported `client_lessor_isEtcdLease`) and `NewSession`, whose contexts come from
`client.Ctx()` = `WithCancel(TODO())` (the trusted `WithCancelTodo` axiom, whose post has no
`Value` fact: a trusted change beyond the lists). Both were reverted on the branch; proposed
for premise-fixes-8 with `Invoke`/`NewStream` (same key, same contexts). Untouched:
`streamKeyFromCtx`, `FromOutgoingContext`, `watchCtx`.

## Next, in order

1. After the decision: either pf8 takes D5/FromOutgoingContext, or this stage does the ripple.
2. Checkpoint (b): full build (flock, 64G), tcb `--check --update` (-1 axiom expected),
   collections, interfaces, gen-init `--check`; notes (decisions entry, STATUS); STOP before
   land.sh.

## Build command

`systemd-run --scope -q -p MemoryMax=64G lake build --packages=/shared/tmp/manifest-ddc.json <targets>`;
lean-check: `LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json etc/lean-check.py -q FILE`.
Item 2 leaves: `Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Results`,
`Proof.go_etcd_io.etcd.cache.v3.Results`, examples `etcd.watch.Served`, `etcd.auth.MainServe`,
`lib.etcdstart.{Defs,ServedLease}`.
