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
