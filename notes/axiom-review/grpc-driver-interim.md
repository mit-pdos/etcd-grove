# Axiom review: the gRPC driver's interim trusted restatements (T1-T9), branch `grpc-trusted-T`

**Reviewed** 2026-11-24, `grpc-trusted-T` at `09d80dfc5a` (diff from `0b97c23ab0`), by an independent
reviewer with the `axiom` skill, given the axiom texts and grpc-go v1.84 / `models/grpc` / etcd's
`retry_interceptor.go`, not the author's reasoning. Go evidence: scratch tests outside the repository
(grpc v1.84.0, go1.27.1): `/tmp/axcx-closed/{main_test.go,md_test.go}`, `/tmp/axcx-size/size_test.go`,
`/tmp/axcx-pt/main.go` (not kept; the programs are quoted below).

| item | verdict (first round) | after the fix |
|---|---|---|
| T1 `status.Error` (+`statusCodeIs err c`, `hasGRPCStatus`) | sound | — |
| T2 `status.Code` (returns the precondition's `c`) | sound (no fromerror-wand form) | — |
| T3 `status.FromError` (`hasGRPCStatus err → ok = true`) | sound | — |
| T4 `grpcInvokerOk` error shape `hasGRPCStatus ∨ eofIs` | sound under `dialOptsAt`'s configurations | — |
| T4 `grpcInvokerDone`, Canceled-context arm | sound | — |
| T4 `grpcInvokerDone`, closed-connection arm | **unsound**: refuted in Go | fixed (below) |
| T5 `cliStreamErr … E`, `streamErrShape` | sound | — |
| T6 `NewStream` | sound; caveat documented | doc |
| T7 `NewClient`, `dialPassthrough` (214 byte cases tested) | sound | — |
| T7 `streamIcMdIs` / etcd's interceptor | sound; doc gap (token fetch) | doc |
| T8 `ClientConn.Close` | statement sound, docstring false (same root as T4) | doc |
| T9 `grpcRepliesBounded` | **unsound** (vacuous) | fixed (below) |

## T4, closed-connection arm — refuted, fixed

The arm promised `Canceled` for any `ctxOk` context and any metadata on a closed connection, resting on
the model's `onCallBegin` failing first. grpc-go v1.84's `OnCallBegin` fails nothing; `newClientStream`
checks the outgoing metadata (`Internal`), runs `waitForResolvedAddrs` (selects on the caller's
context), then `newAttemptLocked` checks the caller's context before `cc.ctx`.
- Counterexample A: `conn.Close()`, then `Invoke` with `AppendToOutgoingContext(ctx, "bad key", "v")`:
  `Internal`; provable not to panic from the old text (`lowerKey "bad key"`, `ctxOk`, `Close.spec`,
  `grpcInvokerDone`, `status.Code`).
- Counterexample B: a `WithTimeout(…, 0)` context on a closed connection: `DeadlineExceeded`.

**Fix:** the premise is now `metadata.outMD ctx none ∗ (ctxCanceledIs ctx ∨ grpcConnClosed conn ∗
ctxQuiet ctx)`; the docstring follows grpc-go's order. The model's `onCallBegin` failing a closed
connection first has fewer behaviors than grpc-go (recorded in the docstring; a model fix is the model
owners').

## T9 — vacuous, fixed

A model's default `wireLen` is `grpcMsgMax` (2^32, "no bound known") and the bound was `<
grpcReplyMax` (2^48): every default model passed, `RangeResponse`'s among them, whose persistent `send`
admits `Kvs` sharing one large `KeyValue` (an encoding ~2^49 bytes; grpc's codec's `make` panics, crashing
the server). **Fix:** `Rep.wireLen m < grpcMsgMax`.

## Doc fixes
- T6: with `ClientStreams` false, `SendMsg` returns `nil` on a failed transport write (the send token's
  growth is not delivery there; the server never sees a clean end).
- T7: `streamIcMdIs` says the interceptor may first make its token fetch's unary calls (etcd's `getToken`).
- T8: `Close`'s docstring no longer claims `onCallBegin` fails later calls.

## Second round

Re-attack of `38170fa86d` (same reviewer, read-only): **both fixes sound.**
- `grpcInvokerDone`: counterexample A excluded by `outMD ctx none`, B by `ctxQuiet` (a timer context's
  `Done()` is not nil); the closed-connection walk through `newClientStream` (`OnCallBegin`, no metadata,
  `waitForResolvedAddrs`'s nil `ctx.Done()` arm, the default `SelectConfig`, `before`, the default codec,
  `newAttemptLocked`'s `cc.ctx` check) ends in `ErrClientConnClosing`. Caveat (doc, applied): it relies on
  the service config setting no method config (a `timeout` would give `DeadlineExceeded`); now stated in
  `grpcInvokerDone` and `grpcResolverAt`.
- `grpcRepliesBounded` at `< grpcMsgMax`: every registered reply model keeps the default `wireLen` but
  `StringValue`'s (`s.length + 11`, a true bound on protobuf-go's `Size`, `send` pinning no unknown fields).
  Caveat (doc, applied): an explicit reply `wireLen` is trusted, reviewed as a size bound at registration.

## T12 `srvNotEof` (2026-11-25, `b8c33ac280`, a fresh reviewer)

The server end's `RecvMsg`/`Recv` generic-error arm (`srvRawStreamIs`, `srvRawStreamIsW`, `srvStreamIs`)
gains `srvNotEof err` (`□ ∀ e, eofIs e -∗ ⌜err ≠ e⌝`). **Sound**, with caveats (none breaks it):
the model queues `io.EOF` only at `frameClose` (`model_transport.go:895-900`), every other end being a
`connectionError` or a context status, and the receive queue keeps its first end; real grpc-go v1.84 queues
`io.EOF` only on END_STREAM (`http2_server.go:532-535`, `:832-835`); a cut message is
`io.ErrUnexpectedEOF`, decoding errors are statuses; after END_STREAM and an RST real grpc-go may give
`Canceled` where the model gives EOF (generic arm, fine). Caveats: the docstring's "`toRPCErr` makes a
status" missed the unconverted second read of a non-client-streaming method (text fixed); partial
messages are unreachable in the model; `Server.ServeHTTP`'s transport returns `io.EOF` at a body's end
and is outside the axiom (noted in the docstring).

## T4 `grpcInvokerDone` at the connection's resource (merge of lean, 2026-11-25; not yet reviewed)

Lean's decision 1b runs every call on an etcd connection at `clientRes` (`levelTok 0`), and its
`grpcInvokerOk_of_chainRes` builds `grpcInvokerOk` for a chain's invoker callable only with that token:
the resource-free `grpcInvokerDone` could not be met. `grpcInvokerDone conn Ok inv` now lends
`⌜Ok R⌝ ∗ R` (back untouched in the post), as `grpcInvokerOk`'s attempt triple does. The old triple
implies the new one (frame `R`), so the axioms giving `grpcInvokerOk` promise no more than before; the
driver's `plain_Invoke_done` uses it at `R := True` (`anyRes`).
