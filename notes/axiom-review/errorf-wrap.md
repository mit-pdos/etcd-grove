# `fmt.ErrorfWrap` and the handler contracts at `srvErrOk` (errorf-wrap, 2026-11-06)

**Reviewed** (draft statements, `/shared/tmp/errorf-wrap-package.md`; not yet in the tree):
- N1, the new axiom `fmt.ErrorfWrap.wp_proof`. Its post is disjunctive (etcd-grove-82's decision,
  2026-11-06): Perennial's model `fmt.modelErrIs`, or Go's `*fmt.wrapError` `fmt.wrapErrIs`.
- N4, the meaning of `grpc.Server.Serve.wp_proof`, `grpc.Server.RegisterService.wp_proof` and
  `grpc_prometheus.ServerMetrics.UnaryServerInterceptor.wp_proof`. Their handler contracts
  (`grpcHandlerOk*`, `grpcMethodOk*`, `srvInterceptorOk`) now admit a handler error that is
  `srvErrOk` (`statusErrOk ∨ ctxWrapErr`), not only `statusErrOk`.

Go at go1.27.3 (`src/fmt/errors.go:23-81`); grpc and grpc-prometheus at the examples module's pins.

**Verdict: survives** every attack tried. Tests: `examples/axiomcx/wrapctx/{wrapctx,n1}_test.go`
on branch `axiom/hs6-wrapctx`; log `gotest-n1.log`; all pass.

## N1's claims, each checked in Go (`TestN1Claims`)

Each claim is checked as `if !claim { panic }`. The calls checked are `Errorf(pre+"%w", inner)` for
`inner` ∈ {`Canceled`, `DeadlineExceeded`, `errors.New("x")`}, at one level and at two (the Txn
chain):
- **A pointer error:** `reflect.TypeOf(e).Kind() == Pointer` (`*fmt.wrapError`). Allocated fresh by
  `&wrapError{msg: s}`.
- **`Unwrap() error` returns `inner`**, the same interface value (`==`). It is `w.err, _ =
  a[i].(error)`, a copy taken before `Errorf` returns: overwriting `args[0]` afterwards does not
  change it.
- **No `Unwrap() []error`, `Is`, `As` or `GRPCStatus`.** The type assertions fail. The method set,
  enumerated, is `Error` and `Unwrap` only (`errors.go:75-81`).
- **`Error()` returns one string**, the same at every call (`return e.msg`), beginning with `pre`.
  At `pre` without `%`, `doPrintf` copies `pre` verbatim and formats `%w` as `%v` of the error
  (`Error()`).

## The premises' edges (what Go does outside them)

- **A nil argument:** `"p: %!w(<nil>)"`, still a `*wrapError`, `Unwrap` nil. Excluded by `inner :
  GoInterfaceOk`.
- **An `Error()` that panics:** `fmt` recovers it, giving `"p: %!v(PANIC=Error method: boom)"`. The
  prefix still holds. Excluded anyway by `fmt.stringMethodSpec inner`.
- **A `%` in `pre`:** `"100%% p: …"` formats as `"100% p: …"`, so the prefix claim would fail. This
  is why the premise `(W8 37) ∉ pre` is needed.
- **No `%` and no args:** the fast path, `errors.New(format)`, never a `*wrapError`. `pre ++ "%w"`
  always has a `%`, so the path is unreachable.

## The left side: consistency with the trusted model

Perennial's `fmt.Errorf` model is `errors.New(format)`: an `*errors.errorString` whose `Error()`
returns. That is exactly `fmt.modelErrIs`. The axiom therefore holds of the model's body as well as
of Go, and contradicts neither.

The first draft's post (Go's side only) stated what the model refutes on the same call. That was a
trap for later proofs even though WP's non-conjunctivity blocks the obvious derivation. The
disjunction removes it.

## N4: Go's server with a handler returning `ctxWrapErr` errors

`wrapctx_test.go` serves `Range` through `grpc.NewServer(ChainUnaryInterceptor(grpcprom
.UnaryServerInterceptor()))`, `RegisterKVServer`, `Serve` on a bufconn and a client call. The
handler returns `togRPCError(err)` for:
- one level over `Canceled`/`DeadlineExceeded` (`TestCanceled`, `TestDeadlineExceeded`);
- the Txn chain over each (`TestTwoLevelServer*`).

For every case:
- **`togRPCError` passes it through.** `errors.Is` walks the `Unwrap` chain to the context error.
  For a non-context `inner` it does not (`TestN1Claims`), as the map/`Unknown` branches say.
- **prometheus's `PostCall`:** `status.FromError(e)` gives `ok = false`, `Unknown`, the full
  message, no panic. Its `errors.As` walks the chain, and no node has `GRPCStatus` or `As`.
  `status.Code(e)` gives `Unknown`.
- **grpc's server:** `FromError` is not ok, then `status.FromContextError(e)` gives `Canceled` or
  `DeadlineExceeded` (it uses `errors.Is`). The client receives that code, with the message as the
  description.
- **`RegisterService`:** registration (`RegisterKVServer`) and dispatch through the generated
  handler `_KV_Range_Handler` and the interceptor chain. No panic.

The client's description is never `futureRevDesc`/`compactedDesc` (`rpctypes.Error(err)` is
neither). This is recorded for 7c-2 part 2, whose `handlerDescs` will make descriptions matter.

## Not tried

- `ServeHTTP` (etcd's TLS path), which is unmodelled: the 7c plan's "7c: left".
- `wrapErrors` (two or more `%w`), which no caller uses and N1 does not cover.

## N1a (2026-11-06, k8s etcd3 7c-2 part 2): both sides give the prefix

`fmt.modelErrIs` takes `pre`. Its `Error()` now returns `pre ++ s` for some `s`, the same as
`wrapErrIs`'s. Both sides were checked against N1's premises (`(W8 37) ∉ pre`, `inner :
GoInterfaceOk`, `stringMethodSpec inner`).

- **The model's side.** Perennial's `fmt.Errorf.impl` is `λ format a, errors.New(format)`
  (`Perennial/TrustedCode/fmt.lean:27`). `errors.New` is translated Go. Its proved spec
  `errors.New.spec` (`Perennial/Spec/errors/New.lean`) gives an `Error()` that returns `msg`, which
  is `format = pre ++ "%w"`. So the model holds with `s = "%w"`, whatever the premises are.
- **Go's side.** `s = inner.Error()`: `doPrintf` copies `pre` byte for byte (it has no `%`) and
  formats `%w` as `%v` of `inner`. TestN1Claims checks the prefix one level and two levels deep.
  At the premises' edges the prefix still holds or the case is excluded (above, "The premises'
  edges"): an `Error()` that panics still gives `pre ++ "%!v(PANIC=…)"`. A `%` in `pre` is the one
  case that breaks the prefix, and the premise excludes it.

**Verdict: survives.** The disjunction's two sides now say only what they share about `Error()`.

## N1b (2026-11-06, k8s etcd3 7c-2 part 2): the returned error's description begins with `pre`

The post of `fmt.ErrorfWrap` gains `⌜pre <+: errDesc (ok err)⌝`. `errDesc` is the opaque gRPC
description of D29. Its declaration moved, unchanged, to
`Proof/google_golang_org/grpc/status/ErrDesc.lean`.

**Truth of Go** (`n1b_test.go`, `TestN1bDescPrefix`, log `gotest-n1b.log`; branch
`axiom/hs6-wrapctx` 92a14256c9). Cases: `inner` ∈ {`Canceled`, `DeadlineExceeded`,
`errors.New("x")`}, at one level and at two (the Txn chain). On every path that produces a
description, the description begins with `pre`:
- `rpctypes.ErrorDesc(e)`;
- `status.Convert(e).Message()`, which goes through `FromError` → `Unknown` with `e.Error()`, since no
  node of the chain has `GRPCStatus`;
- `status.FromContextError(e).Message()` for a context `inner`, the server's path;
- `ErrorDesc(togRPCError(e))`;
- the description a client of a real grpc server receives from a handler returning
  `togRPCError(e)`.

**The model's side.** `errors.New(pre + "%w")`, Perennial's model of the call, has an `errDesc`
(through D29: a non-status error's description is its `Error()`) of `pre + "%w"`. Checked in the
same test (`"rangeKeys: context cancelled: %w"` on every path).

**Consistency.** A contradiction needs two incompatible prefixes of the same error's description.
- **As a law it would be inconsistent.** `errorfWrapIs ii _ pre ⊢ ⌜pre <+: errDesc (ok ii)⌝` is
  false because WP is partial: a user type whose `Error()` loops satisfies `wrapErrIs` at every
  `pre`. N1b is therefore stated only of the error the call returns.
- **Reusing a returned error with another `pre`.** No triple gives a second prefix of an error that
  is already returned. A second call returns a new error: Go's `&wrapError{…}` and the model's
  `errors.New` both allocate, and the test checks `e3 ≠ e, e2`. The post gives `err`
  existentially, and nothing relates it to an earlier error.
- **Aliasing.** The two levels of the Txn chain are two errors with two prefixes. The outer's
  description `p2 ++ p1 ++ …` begins with `p2` only; nothing claims `p1` of it.
- **A looping `inner.Error()`.** It satisfies `stringMethodSpec inner` (WP is partial). Go's
  `Errorf` then never returns, so the post is vacuous.
- **Across executions.** `errDesc` is opaque, so every proof is valid for every interpretation of
  it. A pointer that is reused across runs therefore needs a consistent `errDesc` within one run
  only, and Perennial's semantics never reuses a location within a run.

**Verdict: survives.**
