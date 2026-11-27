/-
`(*kv).Get(ctx, key, opts...)` by a client of members at other machines, at the cluster view: an interim trust-boundary axiom
(`notes/etcd-dist-plan.md` §18.4). The real Go is translated; the cross-machine proof needs #24's S2 client
side, which retires it. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.KVGetDist

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- **`(*kv).Get(ctx, key, opts...)` across machines** (interim trust boundary until #24's S2 client side; see the spec). What
it asserts of clientv3 v3.6 and grpc-go v1.84 (the model) over the net extension.

**Why it is an axiom** (the standing rule's order): the real Go is translated (clientv3 v3.6 with bodies,
grpc-go v1.84's model `models/grpc`), and in one process it is proved (`kv.Get.spec`, over `Invoke`'s
registration, `isGrpcRpcsMd`/`kvRegsAt`). Across machines the call goes through grpc's `Invoke` over the
net extension: the S2 interface exists (`grpcAddrAt`, the opaque `grpcCliPI`/`grpcSrvPI`), but no proof
establishes the protocols of any bytes and `etcdSvc` has no law, so nothing can be proved over it yet: the
cross-machine proof needs #24's S2 client side (`notes/phase7-plan.md` §1.3, §2.4). A Go model with the same
behaviour is the grpc model itself (the same gap), and a trusted stand-in for clientv3 and grpc would still
need the wire proof and trust more than a contract per function (`notes/etcd-dist-plan.md` §18.4).

**Why it is true.** It is `kv.Get.spec` with `isKv api Γ.kv _` replaced by `kvClientAt` (the address
facts at `Γ`) and the error arm's `kvErr err` weakened to `statusErrOk err` (2026-11-26, F6: the cache's
watch loop prints `Get`'s error with `fmt`'s `%v`), in any auth mode:
* *Who answers.* The client dials the endpoints themselves: `clientNoProxy` (`grpc.WithNoProxy()` in its
  configuration: grpc-go never wraps the resolver in its proxy-resolving `delegatingresolver` nor dials
  through an HTTP `CONNECT` proxy named by `HTTPS_PROXY`; review F1, `TestProxyRogue`, `TestWithNoProxyFix`).
  Each endpoint's table is set once by the start (`etcdAddr_set` spends `addrUnset`) and answered successfully only by
  `Serve_dist` at a member whose KV names are `kvCongr` to `Γ.kv`; `bridge.New` consumes `netAddrLeft`
  (review 4). Another program at the address (a raw listener, an empty gRPC server, the only server that
  serves the opaque table without its handlers) answers no call successfully: the error arm. So every reply is a real member's handler, at KV names `kvSame` to `Γ.kv` (what `isKv_intro`
  asks of each member), and the handler's spec is the one its in-process proof meets.
* *Errors, timeouts, retries are the error arm.* A deadline, a partition or a crashed member is
  `err ≠ nil`, of which only `statusErrOk` is claimed. A range is retried on `Unavailable` at the next endpoint
  (`isSafeRetryImmutableRPC`), and also after a per-attempt context error, a learner's refusal or a token
  refresh; the read update is persistent (`□`), as in `kv.Get.spec`, so a retried or repeated read fires it
  again harmlessly. A serializable range carries no update (its post `True`).
* *Why a remote call's error is `statusErrOk`.* No error value crosses the network: every error `Get`
  returns is built at the caller's machine, by the same client code as in one process, where `kv.Get.spec`
  proves it. `kv.Get` returns `ContextError(ctx, err)` of `kv.Do`'s error (itself already a `ContextError`
  of the stub's error or of `ErrInvalidSortOption`: the same set of results): `nil`; `rpctypes.Error`'s
  `EtcdError` (a value of etcd's own leaf type, chosen by the status message among etcd's fixed error
  strings) or the error itself; for a status of code `DeadlineExceeded` or `Canceled`, `ctx.Err()` when
  it is non-nil (`ctxErrClient`: the caller's context's errors are `statusErrOk`). `kv.Do`'s error is
  `rpctypes.ErrInvalidSortOption` (an `EtcdError`, a package variable) or the stub's `Invoke` error through the
  client's interceptors: grpc-go's `*status.Error`, built at the caller from a status code, message and
  details (the reply's trailers, whose `grpc-status-details-bin` proto, if its code agrees, supplies the
  message and details; or the transport's or the context's failure, `status.Error`/`FromContextError`),
  or the retry interceptor's own: `waitRetryBackoff`'s `status.Error` of `ctx.Err()`'s message, or a token
  refresh's `Authenticate` error (itself a `ContextError` of a call of these kinds). All are leaves (no `Unwrap`/`As`) with a fixed `Error()` and no `Format`,
  as `statusErrOk` asks (`Error()` reads only the code and message); the remote member's handler only
  chooses the code, message and status details. Not claimed:
  `kvErr`'s `clientErr` and `errCellOk` (review `notes/axiom-review/kv-get-dist-statuserr.md`).
* *What a success claims* is `kv.Get.spec`'s post, which the in-process proof derives from the member's
  handler spec at its names through `kvSame`: the reply's fields as functions of the state the update fired
  at, the selection, count and header revision of the state the read linearized at (a linearizable range), or of some state (serializable).

Retired by #24's S2 client side: `etcdSvc` defined (each entry the member's handler spec at its names),
`Invoke` over the net model, and this statement proved from `kv.Get.spec` over an `isKv` built from the
registration (`isKv_intro`, `kvSame` from `Serve_dist`'s `kvCongr`). The statement does not change. -/
axiom KV_Get_dist.wp_proof : KV_Get_dist.spec (GF := GF) (hG := hG)

end proof

end etcd_dist
end EtcdGrove
end Perennial
