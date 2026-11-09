/-
## `traceutil.Tracer.Start(ctx, name, opts...)`: assumed (otel)

**Users.** The server's request entry points (`v3_server.go:108,160,297,312,329,384,441,472,490`,
`defer span.End()`), the watch stream (`v3rpc/watch.go`). Snippet: `trace.go` (`ReqRequestTrace`).

**Assumed** (otel is translated names-only). The package variable `Tracer` holds the tracer
`noop.NewTracerProvider().Tracer(...)` from the package's initialization (`tracerAt`, a law of the
package's init, `tracer_init.spec`), or the one `traceutil.Init` installs (`embed`, with distributed
tracing configured: outside this scope, see `tracer_init`). otel's tracers return
`ContextWithSpan(ctx, s)` (a `WithValue` at otel's key `traceContextKeyType`) and the span `s` (the
SDK's: a new span; the no-op tracer's: its no-op span, or, when `ctx`'s span is not recording, `ctx`
itself and `ctx`'s span). They call `SpanContext()` (and the no-op one `IsRecording()`) on `ctx`'s
span: `ctxSpanOk ctx` (that span, if any, is a genuine otel span) is what makes that safe.

**Changes.** From `specs-ref`'s `Tracer__Start.lean`: over W0's context vocabulary (`ctxOk`,
`ctxWithValues`, `ctxValueAt` at otel's key type) in place of the descriptor and the list of each
package's facts (grpc's metadata, the start time, the trace): each package's "another key" law
carries its own; the span is `OtelTrace.spanOk`.

**Margin.** None beyond the scope (no `Init`).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.Api
public import Spec.go_opentelemetry_io.otel.trace.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace TraceUtil

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.traceutil.Assumptions]

/-- **A span and a context carrying it** (`ctx` itself, or a `WithValue` of it at otel's key). -/
def Tracer.Start.spec : Prop :=
  ∀ (tr : GoInterfaceOk) (ctx : GoInterface) (name : GoString) (opts : GoSlice),
  {{ tracerAt (GF := GF) tr ∗ Context.ctxOk ctx ∗ OtelTrace.ctxSpanOk ctx }}
    (App (App (App (Val #(methods tr.ty go!"Start" tr.v)) (Val #ctx)) (Val #name)) (Val #opts))
  {{ (ctx' : GoInterface) (sp : GoInterface), RET (PairV #ctx' #sp);
      Context.ctxOk ctx' ∗ OtelTrace.ctxSpanOk ctx' ∗ OtelTrace.spanOk sp ∗
      (⌜ctx' = ctx⌝ ∨ Context.ctxWithValues ctx ctx' ∗
        ∃ k : w64, Context.ctxValueAt ctx ctx'
          (interface.mkOk go_opentelemetry_io.otel.trace.traceContextKeyType.ty #k)) }}

end spec
end TraceUtil
end EtcdGrove
end Perennial
