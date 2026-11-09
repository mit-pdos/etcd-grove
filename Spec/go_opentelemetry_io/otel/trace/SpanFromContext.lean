/-
## `trace.SpanFromContext(ctx)`: assumed

**Users.** `EtcdServer.raftRequest` (`v3_server.go:1015`: `RecordError` on a failed proposal).
Snippet: `examples/specreq/pkgleaves/trace.go` (`ReqRequestTrace`).

**Assumed**: otel's `trace/context.go`: `ctx == nil` gives the no-op span; else `ctx.Value
(currentSpanKey)` as a `Span` (comma-ok), or the no-op span. `ctxSpanOk ctx`: that value, if any, is
a genuine span, and the `Value` call returns.

**Changes.** From `specs-ref`'s `Spec/go_opentelemetry_io/otel/trace/SpanFromContext.lean` (whose
`isContext` arm was refuted): the premise is `ctxSpanOk`.
-/
module

public import Spec.go_opentelemetry_io.otel.trace.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace OtelTrace

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_opentelemetry_io.otel.trace.Assumptions]

/-- **The span `ctx` carries** (or the no-op span): a span. -/
def SpanFromContext.spec : Prop :=
  ∀ (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.trace ∗ ctxSpanOk ctx }}
    (App (Val (@! go_opentelemetry_io.otel.trace.SpanFromContext)) (Val #ctx))
  {{ (sp : GoInterface), RET #sp; spanOk sp }}

end spec
end OtelTrace
end EtcdGrove
end Perennial
