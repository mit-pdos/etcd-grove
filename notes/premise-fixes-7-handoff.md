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

## Blocker (STOP, waiting for etcd-grove-81)

`Watch` returns `rpctypes.ErrGRPCWatchCanceled`; its init axiom (`ErrGRPCWatchCanceled_init`,
generated from `etc/gen-init.py`'s `_RWERRS`) gives only `errorStringSpec`, not `statusErrOk`
(the Scope assumed it did). The `Watch` proof has a placeholder `sorry` for
`srvErrOk (ok eWC)` (search `HsvW`). Proposed fix (trusted change): `ErrGRPCWatchCanceled_init`'s
post gains `statusErrOk (GoInterface.ok e)`, as the HS-6 `ErrGRPC*` posts; then `rpctypesInit`
(cache `Base.lean`) and v3rpc's `watchPkgVars` carry it.

## Next, in order

1. After the decision: the init change (gen-init.py, regenerate Init files), remove the `sorry`,
   build item 2's leaves, commit. Checkpoint (a).
2. Item 1 (Scope A.2-A.5, client and k8s only).
3. Checkpoint (b): full build (flock, 64G), tcb `--check --update`, collections, interfaces,
   gen-init `--check`; notes; STOP before land.sh.

## Build command

`systemd-run --scope -q -p MemoryMax=64G lake build --packages=/shared/tmp/manifest-ddc.json <targets>`;
lean-check: `LAKE_OPTS=--packages=/shared/tmp/manifest-ddc.json etc/lean-check.py -q FILE`.
Item 2 leaves: `Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Results`,
`Proof.go_etcd_io.etcd.cache.v3.Results`, examples `etcd.watch.Served`, `etcd.auth.MainServe`,
`lib.etcdstart.{Defs,ServedLease}`.
