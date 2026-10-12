/-
`trace.SpanFromContext`: the trust boundary (`go.opentelemetry.io/otel/trace` is names-only).
Lean-first (no Rocq counterpart). mvcc's `watchStream.Watch` takes the span of its context and
ends it when the watcher is cancelled (`defer span.End()` in the cancel closure it stores).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Base
public import GeneratedProof.go_opentelemetry_io.otel.trace
public import Perennial.Proof.context

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_opentelemetry_io.otel

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `sp` is a `trace.Span` (persistent): a non-nil interface value whose `End()` returns
(tracing has no effect here). `End` is variadic (`options ...SpanEndOption`); the call
`span.End()` with no option is passed `#()` by Goose's deferred call (the form `Watch`'s cancel
closure has), so the triple is about that call. -/
def trace.isSpan (sp : GoInterface) : IProp GF :=
  iprop(∃ si : GoInterfaceOk, ⌜sp = GoInterface.ok si⌝ ∗
    □ ({{ True }} (App (Val #(methods si.ty go!"End" si.v)) (Val #())) {{ RET #(); True }}))

instance trace.isSpan_persistent (sp : GoInterface) : Persistent (trace.isSpan (GF := GF) sp) := by
  unfold trace.isSpan; infer_instance

/-- `trace.SpanFromContext(ctx)` (a context) returns a span. -/
abbrev trace.SpanFromContext.spec : Prop :=
  ∀ (ctx : GoInterfaceOk) (cd : context.ContextDesc (IProp GF)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_opentelemetry_io.otel.trace ∗ context.isContext ctx cd }}
    (App (Val (@! trace.SpanFromContext)) (Val #(GoInterface.ok ctx)))
  {{ (sp : GoInterface), RET #sp; trace.isSpan sp }}

end spec

end EtcdGrove
end Perennial
