/-
`tracing.Start(ctx, name, attrs...)` (`k8s.io/component-base/tracing`, names-only): a span, and
a context derived from `ctx` (OpenTelemetry's `ContextWithSpan`, a value context: its `Done` and
`Err` are the parent's), so a context the client accepts (`ctxOk`, `ctxErrClient` at the parent's
description) gives one too. Tracing is otherwise a no-op for the store's results. The trust boundary: an axiom, `Proof/k8s_io/component_base/tracing/Start.lean`. Lean-first (no Rocq
counterpart).

A context whose `Done()` is `nil` gives one too (k8s 7e-2, blocker B2, decided by etcd-grove-81:
`ctxNeverDone`): OpenTelemetry's `Tracer.Start` (the noop tracer's and the SDK's) and
`utiltrace.ContextWithTrace` return `context.WithValue` contexts, whose `Done` is the parent's;
checked at the pin by `examples/k8s7e2attack`'s `TestTracingStartDoneNil` (from
`context.Background()`, noop tracer) and `TestTracingStartDoneNilSDK` (an SDK tracer provider's span
in the context).

(premise-fixes-7, 2026-11-11) It calls `trace.SpanFromContext(ctx).TracerProvider().Tracer(...)
.Start(ctx, ...)` and `utiltrace.FromContext(ctx).Nest(...)`, so it takes the context's k8s values
well formed (`k8sctx.k8sCtxOk`: a span whose `TracerProvider` panics, or a misbehaving `Value`,
panics, `examples/premisefix/k8sctx`), and the context it returns has them too: otel's new span
(`otelSpan`) under `currentSpanKey`, `utiltrace`'s nested trace (`builtTrace`) under
`ContextTraceKey{}`, the parent's answer at every other key (`context.WithValue`).

(The narrowing of `trace.otelSpan`, 2026-11-13, decided by etcd-grove-81; `notes/otelspan-narrow.md`)
The new span is made by the parent span's `TracerProvider()` (otel's no-op provider when the context
holds none), which `otelSpan` (of the parent) says is a provider of otel's own components, so the
new span is one too; and only such a provider's components run on `ctx` inside `Start`: they read no
key but otel's `currentSpanKey`. A span of a provider with a sampler, ID generator or span processor
of the program's own met the premise before and made `Start` panic (the axiom review's
`TestReviewSamplerReadsKey`, `TestReviewProcessorReadsKey`; such components reach the context at their
own key: `examples/premisefix/k8sctx`'s `TestOtelExcludedComponents`); it is no `otelSpan` now.

(The context sweep's fixes, 2026-11-13, decided by etcd-grove-81; `notes/ctx-sweep-fixes.md`)
`k8sCtxOk` includes `runtime/trace`'s key (`rtrace.traceKeyAny`, `rtrace.taskRes`: not a `*Task`, or
a non-nil one): with an SDK span in the context and Go's execution tracer on, the SDK's
`tracer.Start` calls `runtime/trace.NewTask(ctx, ...)` (`recordingSpan.runtimeTrace`), which reads
`ctx.Value(traceContextKey{})` and the parent task's `id`; a context whose `Value` panics there, or
answers a typed-nil `*Task`, met the premise and made `Start` panic
(`examples/premisefix/k8sctx`'s `TestStartRuntimeTraceKeyPanics`). The returned context answers there
`NewTask`'s fresh `*Task` (tracer on) or the parent's answer (`TestStartRuntimeTraceTask`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Calls
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Proof.k8s_io.component_base.tracing.Defs
public import Proof.k8s_io.apiserver.pkg.audit.CtxKeys

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev tracing.Start.spec : Prop :=
  ∀ (ci : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)) (name : GoString) (attrs : GoSlice),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_base.tracing ∗ ctxOk ci cd ∗
      ctxErrClient ci cd ∗ k8sctx.k8sCtxOk ci }}
    (App (App (App (Val (@! k8s_io.component_base.tracing.Start)) (Val #(GoInterface.ok ci)))
      (Val #name)) (Val #attrs))
  {{ (ci' : GoInterfaceOk) (sp : Loc), RET (PairV #(GoInterface.ok ci') #sp);
      ⌜sp ≠ null⌝ ∗ ctxOk ci' cd ∗ ctxErrClient ci' cd ∗ k8sctx.k8sCtxOk ci' ∗
      □ (ctxNeverDone (GoInterface.ok ci) -∗ ctxNeverDone (GoInterface.ok ci')) }}

end spec

end EtcdGrove
end Perennial
