# Axiom review: the attempt contract at the filled `handlerDescs` (invoker-filled, 2026-11-06)

**Reviewed**: `grpcInvokerOk`'s handler-error clause (`Proof/google_golang_org/grpc/InvGrpc.lean`,
`grpcInvokerOk`, `handlerDescs`), stated by the one axiom `grpc.ClientConn.Invoke.wp_proof`
(`Proof/google_golang_org/grpc/ClientConn__Invoke.lean`). This was done at `k8s-etcd3-7c`
`47b8892ff2`, where `handlerDescs = [futureRevDesc, compactedDesc]` (`bac7509e67`). HS-5 (a) is in
place (`ctxErrs`, `perRPCCredsOk`). The claim under review: an attempt error whose description
(`errDesc`) is in `handlerDescs` is the handler's own, and carries the caller's `Ψe`.

Versions: grpc-go v1.84.0 (the examples module). The etcd client is the fork at the pin
`673da07c8fab` (module cache `github.com/upamanyus/etcd/client/v3@v3.0.0-20261103162249-673da07c8fab`;
`.lake/go-src/etcd` is at `249d76bea7` and was not used). Go is go1.27.3.

## Verdict

**Refuted, with a counterexample proved.** The path that breaks the clause is not a new grpc path.
The flaw is in `errDesc` itself: the contract and the handler posts assume it is a function of the
error value (D29), and it is not. `status.FromError.wp_proof`
(`Spec/google_golang_org/grpc/status/FromError.lean`) states this assumption:
- `Message()` returns `errDesc err`;
- for a non-status error, `Error()` returns `errDesc err`.

Go's `FromError` calls `err.Error()` at every call (`status/status.go:126`). `statusErrOk` admits a
leaf error whose `Error()` reads mutable state, because `errorStringSpec` only says that `Error()`
returns some string.

So the following handler (the Go function `Handler` in `examples/axiomcx/flipdesc`) breaks the
clause:
1. It returns such an error `e`.
2. Before returning, it learns `errDesc e = "x"` from `FromError`. Its post's
   `errDesc e ∈ handlerDescs -∗ Ψe …` therefore holds vacuously, and it owes no `Ψe`.
3. It then flips `e`.
4. grpc's `processRPC` calls `FromError(appErr)` again (`server.go:1461`) and sends
   `compactedDesc`.
5. The client's attempt contract hands out `Ψe compactedDesc`, which no handler gave.

The same flaw affects `statusCode`, through a `GRPCStatus()` that reads state, and the
`errors.Is`-on-leaf axiom ("equal errors have equal descriptions").

### Go evidence (`go test -v ./axiomcx/flipdesc/`, this branch)

```
TestMain_: Main panicked: errDesc is not a function of the error
TestAttempt: attempt error: rpc error: code = Unknown desc = etcdserver: mvcc: required revision has been compacted (runs 1)
             Get error: etcdserver: mvcc: required revision has been compacted (== rpctypes.ErrCompacted: true)
```

`TestAttempt` serves `Range` with `Handler` behind a real grpc server and calls it:
- through `cc.Invoke`, the attempt error carries `compactedDesc`, although the handler's
  description of its error was `"x"` when it checked;
- through etcd's client, `Get` returns `rpctypes.ErrCompacted` itself.

### Lean (`Proof/github_com/mit_pdos/etcd_grove/examples/axiomcx/flipdesc/Main.lean`)

The theorems:
- `flip_statusErrOk`: `&flipErr{}`, with its `atomic.Bool` in an invariant, is `statusErrOk`.
- `Main.wp_proof (hFE : status.FromError.spec)`: `{{ isPkgInit flipdesc }} Main #() {{ RET #(); True }}`.
  In Go, `Main` takes `FromError(e).Message()`, flips the flag, takes it again, and panics if the
  two differ.
- `Main.wp_axioms`: the same triple, from the axiom itself.

The module builds (`lake build`, log `/shared/tmp/7c-logs/flipdesc-build3.log`) with no `sorry`.
`#print axioms Main.wp_axioms` gives: `[propext, Classical.choice, Quot.sound,
Perennial.EtcdGrove.status.FromError.wp_proof]`.

The Goose project `axiomcx-flipdesc` (`etc/goose.py`) exists on this branch only.

Not run: `etc/tcb-report.py --roots` (it needs a full build). 14 `Proof/` files use
`status.FromError.wp_proof` directly. Every result that reads a description rests on it: D29's
`noRefusal`, 7c's `handlerDescs`, `rpctypes.Error`/`ErrorDesc`.

### Proposed restatement (not applied)

The common fix is to make a described error's `Error()` and `GRPCStatus()` stable. Add to
`statusErrOk`, or to a separate `errDescOk` that `FromError` requires, the condition that every call
of `Error()` returns `errDesc err` (and `GRPCStatus()` a status of `errDesc`/`statusCode`). The
condition is true of:
- `*status.Error`, whose status is immutable;
- `EtcdError`, a value;
- `*errors.errorString`, whose cell is persistent;
- `*fmt.wrapError`, whose `msg` is fixed at creation;
- the context errors.

`FromError`'s post then follows from its premise. Every producer of a non-nil error in the posts
(`grpcHandlerOk*`, `srvInterceptorOk`, `ctxErrs`, `perRPCCredsOk`) carries the condition, and so do
etcd's handlers through those errors' facts.

A cheaper alternative is to require `errorStringSpec` to return `errDesc err`. That changes the
handler and interceptor contracts too.

No Go bug: grpc documents nothing about calling `Error()` once.

## Attacks that failed (grpc v1.84 unless noted)

Client side, a description that grpc builds or forwards with no handler run:
- **Done context.** `status.FromContextError(ctx.Err())` (`clientconn.go:769`, `stream.go:892`) and
  `toRPCErr(ctx.Err())` (`stream.go:551`, `rpc_util.go:1133`) keep the text. They are covered by
  HS-5 for `ctxErrs`.
- **Perennial's `isContext`.** Its `Err()` gives only `Canceled`/`DeadlineExceeded` (`isCtxErr`).
  grpc never calls `context.Cause`. `WithCancel` takes only `isContext` parents, so no custom
  `Err()` is propagated into a model context.
- **Transport.** `ContextErr` (`transport.go:870`) uses fixed or prefixed text. Every client
  `connectionErrorf` is prefixed (`http2_client.go:228-1818`); `toRPCErr` uses `Desc`, also
  prefixed.
- **Balancer and resolver.** round_robin (etcd's resolver's service config) runs pickfirst, whose
  picker returns the raw `ConnectionError` (prefixed `connection error: desc = "transport: …"`),
  `"name resolver error: %v"`, or `"produced zero addresses"`. `picker_wrapper.go:180` wraps it as
  `Unavailable` with that text, and a timeout with `"latest balancer error: "`/`"… while waiting"`.
- **Per-RPC credentials.** A status error passes through (covered by HS-5). A restricted code
  (`OutOfRange`, the code etcd uses for compaction) is rewrapped with a prefix
  (`http2_client.go:697`).
- **Outgoing metadata.** The validation messages are prefixed (`internal/metadata/metadata.go:107-140`).
- **Other client errors** carry `grpc:`/fixed messages: a deadline already past, send/receive size,
  compression, and the framer's `errorDetail`.
- **Retries and hedging.** etcd sets no retry policy. Transparent retry only resends a stream the
  server never handed to a handler.
- **Client interceptors** are inside `chainWP` (proved code), not the contract.
- **Call options** are limited to scalar/`Peer` (`grpcOptOk`). **Dial options** are only the
  descriptor set (`InvDial.lean`).

Server side:
- **grpc's own statuses** are prefixed: unknown service or method, malformed name, the early
  aborts (`http2_server.go:490,569`), `handler_server.go:110,130`, send errors.
- **Decode errors** were already covered (7c1b-grpc).
- **etcd's interceptors** are proved (`interceptorErrsNotRead`). grpc-prometheus was covered by
  hs6.
- **Stats handlers and other neutral server options** cannot set a status.
- **Panics** are not recovered by grpc.
- **The cluster3 bridge** (`forwards`) relays bytes.
- **`grpc-message`** percent-encoding round-trips. Invalid UTF-8 becomes U+FFFD, which never yields
  the ASCII descriptions.

Between the user's call and the attempt, the etcd client's `kv`, `retry*Client` and interceptor are
proved code. `waitRetryBackoff`'s error is `contextErrToGRPCErr` of an `isContext`/`ctxErrs` error.

Not tried: `ServeHTTP` mode (no axiom covers it).
