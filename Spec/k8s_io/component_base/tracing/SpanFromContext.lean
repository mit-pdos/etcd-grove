/-
`tracing.SpanFromContext(ctx)` (names-only; `k8s.io/component-base/tracing/tracing.go`): a new
span (`&Span{otelSpan: trace.SpanFromContext(ctx), utilSpan: utiltrace.FromContext(ctx)}`,
`tracing.isSpan`). The trust boundary: an axiom, `Proof/k8s_io/component_base/tracing/SpanFromContext.lean`.
Lean-first (no Rocq counterpart).

Since 2026-11-06 (found false with otel's `trace.SpanFromContext`,
`notes/axiom-review/otel-spanfromcontext-todo.md`; the user approved fixing axioms as needed) it
takes `tracing.ctxSpansOk ctx` and returns `tracing.isSpan sp` in place of `⌜sp ≠ null⌝`. It took
any `ctx`: a `nil` one panics in `utiltrace.FromContext` (`ctx.Value(...)`), and a context of the
program's own could answer `Value` with a panic, or with a span whose `End` panics, which the span's
`End` (whose axiom took only `⌜sp ≠ null⌝`) then calls. Faithful
(`Proof/k8s_io/component_base/tracing/Defs.lean`'s header has the code): `trace.SpanFromContext(ctx)`
reads `Value(currentSpanKey)`, `nil` or a span (`trace.spanCtxOk`), and returns it if it is a
`trace.Span`, else otel's no-op span; `utiltrace.FromContext(ctx)` reads
`Value(ContextTraceKey{})` (`tracing.utilTraceCtxOk`), a `*Trace` or `nil`. The span's `End` and
`AddEvent` call the otel span's (`trace.isSpan`) and, if non-nil, the `*Trace`'s `LogIfLong` and
`Step`, which return.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base
public import Proof.k8s_io.component_base.tracing.Defs

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
abbrev tracing.SpanFromContext.spec : Prop :=
  ∀ (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_base.tracing ∗ tracing.ctxSpansOk ctx }}
    (App (Val (@! k8s_io.component_base.tracing.SpanFromContext)) (Val #ctx))
  {{ (sp : Loc), RET #sp; tracing.isSpan sp }}

end spec

end EtcdGrove
end Perennial
