# Axiom review: the handler-description contracts of k8s etcd3 7c-1b (grpc runtime)

**Reviewed** 2026-11-06, branch `k8s-etcd3-7c` at `e65c13c6d7`, at the value 7c-1b gives
`handlerDescs` (`Proof/google_golang_org/grpc/InvGrpc.lean`): `[futureRevDesc, compactedDesc]`,
`"etcdserver: mvcc: required revision is a future revision"` and `"... has been compacted"`
(`cache/v3/Base.lean`). `errDesc` (opaque, `Base.lean:54`) gets its meaning from
`status.FromError`'s spec: the status message, or `Error()` for an error with no status. Go:
grpc-go v1.84.0, go-grpc-middleware `providers/prometheus` v1.1.0 over `v2` v2.3.4 (etcd's
`go.mod`), go1.27.3. Program and tests: `examples/axiomcx/grpcdescs/` (this branch), output in
"Go evidence" below.

| claim | verdict |
|---|---|
| 1. `grpcDecOk`: a decode error's description is not a handler's | **survives** |
| 2. `srvInterceptorOk` for grpc-prometheus (`ServerMetrics.UnaryServerInterceptor` axiom) | early-return clause **survives** (vacuous); the axiom is **refuted in Go, Stuck in Lean** on another premise |
| 3. `handlerDescs`/`grpcInvokerOk`: an attempt error with such a description is the handler's | **refuted in Go, Stuck in Lean** (two client-side paths) |

## 1. `grpcDecOk` — survives

`dec` is `wrapUnaryHandler`'s `df` = `serverStream.RecvMsg` (`server.go:1283`, `stream.go:1891`).
Every error it returns is one of: `parser.recvMsg`'s size errors (`"grpc: received message larger
than max ..."`), `checkRecvPayload`'s, `decompress`'s (`"grpc: failed to decompress ..."`,
`"grpc: ... larger than max"`), `recv`'s `"grpc: failed to unmarshal the received message: %v"`
(`rpc_util.go:1064`), the two cardinality violations, or a transport read error through `toRPCErr`:
the stream's context (`ContextErr`: `"context canceled"`/`"context deadline exceeded"`, or a
prefixed `"Unexpected error from context packet"`), `io.ErrUnexpectedEOF`, and in `ServeHTTP` mode
(etcd's TLS mux) `mapRecvMsgError`: an `http2.StreamError` (fixed text) or a `ConnectionError`
of a `net/http` body-read error (no peer-chosen text). The codec is a registered one (only
`proto`). None can equal either description. Control test `TestDecodeErr`.

## 2. grpc-prometheus's interceptor

The clause under review (an early return carries `errDesc err ∉ handlerDescs`) holds vacuously:
`interceptors.UnaryServerInterceptor` (`v2/interceptors/server.go:16-28`) always calls `handler`
once, with `newCtx`, which `reportable.reporter` returns unchanged (`reporter.go:92-130`), and
returns its result. **But** after the handler it runs `PostCall(err)`, which calls
`status.FromError(err)` (`options.go:14`), hence `err.Error()` for a non-status error.
`srvInterceptorOk` lets the handler return any error, so a handler returning an error whose
`Error()` panics makes the interceptor panic where the axiom promises a return
(`TestPromInterceptor`). Not reachable by etcd's handlers (status errors), and the Lean proof is
stuck: a direct call needs `isContext ci cd ∗ grpcRunCtx ci` of a real context, and Perennial
specifies `cancelCtx.Value` only at `&cancelCtxKey` (no spec for another key's lookup). grpc's
server has the same gap (`processRPC`, `server.go:1461`, `status.FromError(appErr)`), so the Serve
axioms' `grpcMethodOk` post should carry it too.

**Restatement proposed:** in `srvInterceptorOk`'s handler continuation (and `grpcHandlerOk`'s /
`grpcMethodOk`'s posts), `⌜err ≠ nil⌝ -∗ statusErrOk err`.

## 3. "grpc never makes one of these itself" — refuted (Go), Stuck (Lean)

Server side survives: `processRPC` sends `status.FromError(appErr)` (or `FromContextError`) via
`writeStatus`; `encodeGrpcMessage`/`decodeGrpcMessage` round-trip ASCII; post-handler errors
(`encode`, send size) carry `"grpc: ..."` text; the etcd strings occur nowhere in grpc v1.84 or in
etcd's unary client path (only `watch.go`'s `Err()`, not an attempt). The client side does not:

- **(a) The caller's context.** `grpcInvokerOk` takes `ctxOk`, which admits `ctxErrs`: `Err()`
  returns any non-nil `clientErr ∧ statusErrOk ∧ errCellOk` once done, e.g. `rpctypes.ErrCompacted`
  (an `EtcdError`). grpc turns a done context's error into `status.FromContextError(ctx.Err())`
  (`clientconn.go:769`, waiting for the resolver; also the retry backoff, `stream.go:892`) = `New(Unknown, err.Error())`: the attempt fails with
  `compactedDesc`, no handler run (`TestCtxAttempt`; through etcd's client, `Get` returns
  `rpctypes.ErrCompacted` itself: `TestCtxClientGet`).
- **(b) Per-RPC credentials.** `perRPCCredsOk` says nothing of `GetRequestMetadata`'s error;
  `getTrAuthData` (`http2_client.go:695-702`) returns a status error unchanged unless its code is
  restricted by gRFC A54 (`OutOfRange` is; `Unknown` is not), so
  `status.Error(Unknown, compactedDesc)` is the attempt's error (`TestCredsAttempt`). etcd's own
  credentials never fail (`credentials.go:69-77`).

Lean sketch (either path): a client of a connection with `grpcInvokerOk` calls a method whose
`Spec` does not constrain `Ψe` (7c-1b's Range spec, picking `Ψe` false at a request no compaction
explains), with (a) a translated `errCtx` meeting `ctxErrs` (its `Err` returns the package variable
`rpctypes.ErrCompacted`, `statusErrOk` by `rpctypes.Error`'s spec) or (b) `statusCreds` meeting
`perRPCCredsOk`; the post's `errDesc err ∈ handlerDescs -∗ Ψe` gives `False`, discharging
`if ErrorDesc(err) == compactedDesc { panic }`. Not done: `handlerDescs` is `[]` at `e65c13c6d7`,
and a closed program also needs `isGrpcRpcsMd` from the Serve axioms (a registered server).

**Restatement proposed:** `ctxErrs`'s error and `perRPCCredsOk`'s error branch carry
`⌜errDesc err ∉ handlerDescs⌝` (true of `context.Canceled`/`DeadlineExceeded`, of k8s's
`channelContext`, of etcd's credentials), or `ctxErrs` narrowed to Go's two context errors.

## Go evidence (`TMPDIR=/shared/tmp GOTOOLCHAIN=go1.27.3 go test -v ./axiomcx/grpcdescs/`)

```
CtxAttempt panicked: ... rpc error: code = Unknown desc = etcdserver: mvcc: required revision has been compacted
Get error: etcdserver: mvcc: required revision has been compacted (== rpctypes.ErrCompacted: true)
CredsAttempt panicked: ... rpc error: code = Unknown desc = etcdserver: mvcc: required revision has been compacted
decode error: rpc error: code = Internal desc = grpc: failed to unmarshal the received message: proto: cannot parse invalid wire-format data
PromInterceptor panicked: panicErr.Error
ok  github.com/mit-pdos/etcd-grove/examples/axiomcx/grpcdescs
```

## The fixes (approved by the user, 2026-11-06, via etcd-grove-82)

- **HS-5 (a)**, for claim 3: `ctxErrs`' errors and `perRPCCredsOk`'s error branch carry
  `⌜errDesc err ∉ handlerDescs⌝`. `handlerDescs` is filled only after this lands (82's gate).
- **HS-6**, for claim 2: the handler continuation of `srvInterceptorOk` and the posts of
  `grpcHandlerOk`/`grpcMethodOk` (and their `Md`/`Own` forms) constrain a non-nil error, so that
  grpc-prometheus's `PostCall` and grpc's server can call `status.FromError` on it. The
  prometheus and Serve axioms are restated with it. A pre-existing finding: the axioms were too
  permissive before 7c.
Each restated axiom is attacked again before 7c's Freeze. The counterexample package
(`examples/axiomcx/grpcdescs`) stays on branch `axiom/7c1b-grpc`.
