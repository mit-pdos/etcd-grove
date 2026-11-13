# The context sweep's fixes (2026-11-13)

A read-only sweep for the user's strong-theorems goal (no refutable axiom under the closed theorems)
looked for landed trust-boundary axioms whose context premise leaves unconstrained a `ctx.Value`
key the modelled Go code reads. Two of its findings are fixed here, as decided by etcd-grove-81
(the net/http-key ones, `RenewHTTP`, `leaseTimeToLive`, `http.WithContext_ok`/`roundTripperOk`, are
k8s 7f-4's: `notes/renewhttp-value-refuted.md`, `notes/leasetimetolive-value-refuted.md`). Both are
bugs in this repository's trusted text, not in the Go code: the Go code is right for every context
Go's `context` package or the libraries build; the premises admitted contexts no real caller passes.

## 1. `tracing.Start.wp_proof`: runtime/trace's key

**The refutation.** `tracing.Start(ctx, name, attrs...)` (k8s component-base `cd2c1afd246a`) calls
`trace.SpanFromContext(ctx).TracerProvider().Tracer(...).Start(ctx, ...)`. `trace.otelSpan` admits
the otel SDK's `*recordingSpan`, whose `TracerProvider` is the SDK's. The SDK's `tracer.Start`
(sdk/trace v1.47.0 `tracer.go:73`) calls `recordingSpan.runtimeTrace(newCtx)`, which, when Go's
execution tracer is on (`rt.IsEnabled()`, `span.go:844-849`), calls `runtime/trace.NewTask(ctx, name)`;
its `fromContext` reads `ctx.Value(traceContextKey{})` and, if that is a `*Task`, its `id` (go1.27.3
`runtime/trace/annotation.go:39, 65`). None of the premises (`ctxOk`, `ctxErrClient`,
`k8sctx.k8sCtxOk`: audit's key, utiltrace's key, grpc's incoming/outgoing metadata and peer, otel's
span key) says anything of that key. So a context whose `Value` panics there, or answers a typed-nil
`*Task`, met the premise, and `Start` panics, against its post. kube-apiserver turns the execution
tracer on in-process through `/debug/pprof/trace` (`--profiling` defaults to true).

**The Go test.** `examples/premisefix/k8sctx/rtrace_test.go`:
`TestStartRuntimeTraceKeyPanics` (an SDK span in the context; `Value` panics at the key, or answers
`(*trace.Task)(nil)`; `Start` returns with the tracer off and panics with it on) and
`TestStartRuntimeTraceTask` (the new fact holds of the parent, `nil`, and of the context `Start`
returns: a fresh non-nil `*Task` with the tracer on, the parent's `nil` with it off; a child started
from the tracer-on context does not panic). Run: `cd examples/premisefix/k8sctx && GOWORK=off
GOFLAGS=-mod=mod go test -run RuntimeTrace -v .` (go1.27.1 at /usr/local/go; the code paths are the
same in go1.27.3).

**Reach.** `etc/tcb-collections/k8s.txt` (client/v3/kubernetes Link, apiserver storage/etcd3 Link)
and `etc/tcb-collections/k8setcd3.txt` (the closed k8s etcd3 theorems, through the store's
`Get`/`Create`/`GetList`/`GuaranteedUpdate`).

**The fix.** `runtime/trace` translated types-only (project `k8s-apiserver`, `Code/runtime/trace.toml`,
lean root `runtime/trace=`), and a third Kubernetes key in `k8sctx.k8sCtxOk`
(`Proof/k8s_io/apiserver/pkg/audit/CtxKeys.lean`):
`context.valueAt ctx rtrace.traceKeyAny rtrace.taskRes`, where `rtrace.taskRes v` says that `v` is
not a `*Task`, or a non-nil one (`fromContext(ctx).id` reads nothing else; a `*Task` outside the
package is `&Task{}` or one `NewTask` returned). `tracing.Start.spec`'s statement is unchanged; its
premise and post both carry `k8sCtxOk`, so the post's `k8sCtxOk ci'` now also says the returned
context's task is not a nil `*Task` (true: `NewTask`'s fresh `*Task`, or `WithValue`'s answer of the
parent's). Producers: `k8sCtxOk_of_nil` (the key added to `k8sKeys`), hence `k8sCtxOk_background`,
`k8sCtxOk_todo`, `k8sCtxOk_bgFrom`, `k8sCtxOk_of_ctxValueNil` (`k8sKeys_notIntPtr`: the key's type is
not `*int`). No new opaque: the fact is pure over translated types.

The sweep's two smaller gaps of the same axiom (MINOR) are not fixed here: (a) the SDK calls every
registered `SpanProcessor.OnStart(ctx, span)`, and `trace.otelSpan` does not exclude a processor
reading context values (the Batch and Simple processors ignore `ctx`); (b) with
`OTEL_GO_X_OBSERVABILITY` set the SDK passes `ctx` to metric instruments (an SDK meter provider reads
only otel's span key).

## 2. `context.WithCancelValCtx.wp_proof`: `&cancelCtxKey`

**The refutation.** The premise on `inctx` is `watchCtx` (`Proof/context/WatchCtx.lean`): `Done()`,
`Err()`, and `Value(mdOutgoingKey{})` in chain form, nothing of `Value` at another key. Go's
`context.WithCancel(&valCtx{inctx})` runs `propagateCancel`; `valCtx.Done()` is the never-closed,
non-nil `valCtxCh`, so it calls `parentCancelCtx(&valCtx{inctx})`, which calls
`parent.Value(&cancelCtxKey)` (go1.27.3 `context.go:388`), promoted from `inctx` (`valCtx` defines
only `Deadline`, `Done`, `Err`), and, if the result is a `*cancelCtx`, `p.done.Load()` (line 392). A
panicking `Value` there, or a typed-nil `*cancelCtx`, makes `WithCancel` panic. The axiom file's
justification ("`parentCancelCtx(&valCtx{inctx})` fails whatever `inctx` is") overlooked the call
and the dereference. The proved `watcher.Watch.spec` takes the same `watchCtx` and inherits it:
`Watch` calls `newWatcherGRPCStream(ctx)`, which runs this `WithCancel` on the caller's goroutine.

**The Go test.** `examples/premisefix/watchctx/watchctx_test.go` (the examples module):
`TestWithCancelValCtxPanics` (`cli.Watch(ctx, "a")` panics with "Value at unconstrained key *int"),
`TestWithCancelValCtxTypedNil` (a nil dereference), and `TestWatchControl` (a context meeting the new
clause, `Value(&cancelCtxKey)` `nil` or a real `*cancelCtx`, and panicking at every other key but
grpc's outgoing metadata: no panic; the watch's client path reads only `[mdOutgoingKey *int]`). Run:
`cd examples && GOWORK=off go test -v ./premisefix/watchctx/`.

**Reach.** `etc/tcb-collections`: authkv, cache-client, cachekv, client, compactkv, k8s,
k8s-compactor, k8scompactor, linkv3p, watch, watchkv. Every closed theorem reaching it builds
`watchCtx` through `watchCtx_of_isContext` (the watch, auth, compactwatch and KMWatch examples;
`watcher.RequestProgress`) or `chanCtx_watch` (k8s compactor's `runWatchLoop`): their premises were
true, the axiom and the exported `watcher.Watch.spec` false as stated.

**The fix.** A fourth clause of `watchCtx`, `"#HCC"`: `isContext`'s `"#HValue"` triple
(`Value(&cancelCtxKey)` returns, and a `*cancelCtx` it returns is a valid one, `isCancelCtxAny`, which
excludes a typed nil; a valid one's `done` is never `valCtxCh`, so `parentCancelCtx` fails). The
producers: `watchCtx_of_isContext` (from `"#HValue"`) and `chanCtx_watch` (`channelContext.Value`
returns `nil`, `chanCtx_valueNil`). The axiom's statement is unchanged (its premise names `watchCtx`);
its file's justification is corrected; `watcher.Watch.spec`, `newWatcherGRPCStream.spec` and
`streamKeyFromCtx.spec` take the strengthened `watchCtx`, noted in their headers.
