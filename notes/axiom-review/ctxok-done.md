# `ctxOk`'s `Done()` (2026-11-10, premise fixes 5)

**Reviewed:** the axioms taking grpc's `ctxOk` (`Proof/google_golang_org/grpc/InvGrpc.lean`), directly
or through a definition: `waitRetryBackoff.wp_proof`, `withVersion.wp_proof`,
`grpc.ClientConn.NewStream.wp_proof`, `grpc.ClientConn.Invoke.wp_proof` (through `grpcInvokerOk`),
`tracing.Start.wp_proof`; at lean `f4e98c54f9`. Found by 7e-1's axiom attack on `waitRetryBackoff`
(`/shared/tmp/k8s7e1/attack-wrb/`). Go: go1.27.3, grpc-go v1.84.0, etcd's client at
`github.com/upamanyus/etcd/client/v3` `a4d2bb1720b9`.

## Verdict

**Refuted, then repaired** (approved by etcd-grove-81 under the user's delegation, 2026-11-10).
`ctxOk` is `isContext ∨ ctxQuiet ∨ ctxErrs`. `isContext` (Perennial's model) states `Done()`
(`#HDone`, `isContextDone`), but `ctxQuiet` stated only that `Err()` returns `nil`, and `ctxErrs` only
Go's contract of `Err()` ("Nothing about `Done()`"). So the axioms that select on `ctx.Done()` covered
contexts on which Go panics:

- `Done()` closed while `Err()` is `nil`: `waitRetryBackoff` takes the `<-ctx.Done()` branch and calls
  `contextErrToGRPCErr(nil)`, whose `err.Error()` dereferences `nil` (`retry_interceptor.go:317-330`,
  `:365-374`);
- `Done()` panicking (a nil pointer receiver): `waitRetryBackoff` panics evaluating `ctx.Done()`;
  so do grpc's `newClientStream` (its goroutine selects on `ctx.Done()`) and transport, under `Invoke`
  and `NewStream`.

Both contexts satisfied the old `ctxQuiet` (and the second the old `ctxErrs` at a never-closed
descriptor). `waitRetryBackoff.wp_proof` proved them panic-free. The test is
`examples/premisefix/ctxdone` (`TestOutsideContractPanics`; the attack's output:
`/shared/tmp/k8s7e1/attack-wrb/out.txt`). No Lean counterexample was built: the Go panic and the
axiom's triple (any `ctxQuiet` context) are direct.

## The repair

- `ctxQuiet ci`: also `Done()` returns the nil channel (`□ ∀ Φ, ▷ Φ #chan.nil -∗ WP ci.Done() {{Φ}}`).
- `ctxDoneCh cd ch`: `ch` is the nil channel, or a broadcast channel (`isBroadcastChanInternal ch γ γi
  Q`) whose done flag means the context is done (`□ (dghostVar γi.doneGn □ true -∗ ContextClosed
  cd.Done_gn)`; then `Err()` is not `nil` by `ctxErrsErr`'s `.Done` case). `ctxDone ci cd`: `Done()`
  returns, without panicking, a `ctxDoneCh`.
- `ctxErrs ci cd := ctxDone ci cd ∗ ctxErrsErr ci cd`, `ctxErrsErr` the old body (the client's
  `ctxErrClient` has it, `ctxErrClient_eq_errs`). `ctxOk`'s text is unchanged.

The producers prove the new clauses: `ctxQuiet_todo`, `ctxQuiet_background` (`emptyCtx.Done` returns
`nil`), `chanCtx_ok` (`channelContext.Done` returns `stopCh`, `wait.channelContext.Done.spec`, whose
done flag is `chanCd`'s closed flag); `quiet_ctx` and `ctxErrClient_quiet` carry them.
`examples/premisefix/ctxdone` checks them on Go's contexts (`TestProducers`, `TestRetryBackoff`).

## The axioms after the repair

| axiom | `ctx` use | before | after |
|---|---|---|---|
| `waitRetryBackoff.wp_proof` | selects on `ctx.Done()`, then `contextErrToGRPCErr(ctx.Err())` | **false** (both contexts) | true: a quiet context's nil channel never fires (the timer does, `nil`); a closed `ctxDoneCh` means the context is done, so `Err()` is a non-nil error with `errorMsgIs` (`statusErrOk`), and `status.Error` of its message is a client error |
| `grpc.ClientConn.Invoke.wp_proof` (`grpcInvokerOk`'s attempt precondition) | grpc's transport selects on `ctx.Done()` | **false** (the panicking `Done()`); with a closed `Done()` and a nil `Err()` grpc plausibly returns an `Internal` status error (`ContextErr(nil)`), not checked | true |
| `grpc.ClientConn.NewStream.wp_proof` | `newClientStream`'s goroutine selects on `ctx.Done()`, `cs.finish(toRPCErr(ctx.Err()))` | **false** (the panicking `Done()`) | true |
| `withVersion.wp_proof` | a value context: `Done`, `Err` its parent's, the same `Done_gn` | true | true (its post inherits the new clauses from its premise) |
| `tracing.Start.wp_proof` | `ContextWithSpan`, a value context; no `Done()` | true | true |

The proved specs taking `ctxOk` (the client's `kv.*`, `lessor.*`, `authClient.*`, k8s's `store.*`,
`Compact`, ...) pass it to these axioms: true, with a stronger premise. No closed statement changes
(the closed theorems build their contexts from `TODO`, `Background`, `isContext` or `chanCtx_ok`).

## Not reviewed here: contexts with no predicate (a finding for a later stage)

Seven axioms take a context with no predicate at all and read `ctx.Value` (or pass it on), so a
context whose `Value` panics would refute them the same way:
`credentials.perRPCCredential.GetRequestMetadata`, `auth.authStore.AuthInfoFromTLS`,
`v3rpc.logUnaryRequestStats`, `metadata.FromIncomingContext`, `audit.GetAuditIDTruncated`,
`kmetrics.HistogramVec.WithContext`, `tracing.SpanFromContext`. Their callers pass grpc's server
contexts or contexts from the model; the repair is a predicate whose `Value` clause is weaker than
`isContext`'s, to design on its own (decided by etcd-grove-81, 2026-11-10: not this stage).

(premise-fixes-7, 2026-11-11) Correction: `perRPCCredential.GetRequestMetadata` does not read `ctx`
(`client/v3/credentials/credentials.go:69-77`); its axiom is true as stated, and its docstring now
says so. The other six are repaired by premise-fixes-7 (`logUnaryRequestStats`,
`GetAuditIDTruncated`, `HistogramVec.WithContext`, `tracing.SpanFromContext`: `Proof/context/LibKeys.lean`,
`Proof/k8s_io/apiserver/pkg/audit/CtxKeys.lean`) and premise-fixes-8 (`FromIncomingContext`,
`AuthInfoFromTLS`).
