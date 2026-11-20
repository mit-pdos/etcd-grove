# `grpclog.SetLoggerV2` and `v3rpc.isClientCtxErr`: premises missing (prove-grpcsmall, 2026-11-20)

Found by reading the pinned code (grpc v1.84.0, the module cache's `google.golang.org/grpc@v1.84.0`;
etcd at the fork's pin), not by the `axiom` skill: no Lean counterexample was built.

## `grpclog.SetLoggerV2.wp_proof`: **false as stated, fixed**

`Spec/google_golang_org/grpc/grpclog/SetLoggerV2.lean` took any `l : val` with precondition `True`
and said the call returns. grpc v1.84.0, `grpclog/loggerv2.go:35-41`:

```go
func SetLoggerV2(l LoggerV2) {
	if _, ok := l.(*componentData); ok {
		panic("cannot use component logger as grpclog logger")
	}
	internal.LoggerV2Impl = l
	internal.DepthLoggerV2Impl, _ = l.(internal.DepthLoggerV2)
}
```

`grpclog.Component(name)` is exported and returns a `*componentData` as a `DepthLoggerV2`, so
`grpclog.SetLoggerV2(grpclog.Component("x"))` panics while the axiom proved it returns. A nil `l`
returns (both assertions are comma-ok).

Fix: the spec takes `l : GoInterface` with the premise
`∀ v, l ≠ interface.mkOk (go.GoType.PointerType grpclog.componentData.ty) v`. Its one caller,
k8s's `etcd3` `init` (`logger.go`, `grpclog.SetLoggerV2(klogWrapper{})`, in the generated
`Proof/k8s_io/apiserver/pkg/storage/etcd3/InitLinked.lean`, `etc/gen-init.py`), discharges it: the
trust-boundary conversion `klogWrapper_toLoggerV2` now returns the interface holding the
`klogWrapper` (`interface.mkOk klogWrapper.ty v`, what Perennial's `convert_to_interface` gives a
non-interface type; it returned some interface), and `klogWrapper_ne_componentData` proves the types
differ. Ledger: `notes/specs-only/ledger.md`, 2026-11-20.

## `v3rpc.isClientCtxErr.wp_proof`: **false as stated, recorded, not fixed**

`Spec/go_etcd_io/etcd/server/v3/etcdserver/api/v3rpc/isClientCtxErr.lean` holds for every
`ctxErr, err` with only `isPkgInit`. The body (`util.go`) returns `true` when `ctxErr != nil`, else
calls `status.FromError(err)`, which calls `err.Error()` (and `GRPCStatus()`) and panics with them. An
`err` whose `Error()` panics, with `ctxErr == nil`, panics in Go; the axiom proves it returns.
`status.FromError`'s own spec was fixed for this (2026-10-14, unit P3a, then fromerror-stable and
fromerror-wand): it requires `statusErrOk err` and a stable `Error()` (`errorMsgIs`).

The premise needed: `⌜ctxErr ≠ nil⌝ ∨ statusErrOk err` (from which `FromError`'s `m` is chosen by
`statusErrOk`'s `∃ m, errorMsgIs e m`). Callers:

- `watchServer.Watch` (watch.go:201): `rerr` from `recvLoop`, whose spec gives `statusErrOk` (ok);
- `serverWatchStream.sendLoop` (watch.go:490, 548, 572) and `LeaseServer.leaseKeepAlive`
  (lease.go:118 a receive error, ok through `srvStreamIs`'s `Recv`; lease.go:149 a send error):
  the errors of the server stream's `Send`, for which `srvStreamIs` (`Proof/google_golang_org/grpc/
  InvGrpcStream.lean`) gives only `streamErr`, not `statusErrOk`.

Discharging it therefore needs `srvStreamIs`'s `Send` error case to carry `statusErrOk` (true of
grpc's `serverStream.SendMsg`, whose errors are status errors, context errors or `io.EOF`, but an
extension of the assumption the trusted server model makes), so it was left for a change that
reviews that assumption. Not reachable from etcd itself: grpc's stream errors have stable,
returning `Error()` methods.
