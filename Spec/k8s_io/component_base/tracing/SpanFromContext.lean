/-
`tracing.SpanFromContext(ctx)` (names-only; `k8s.io/component-base/tracing/tracing.go`): a new
non-nil `*Span` (`&Span{otelSpan: trace.SpanFromContext(ctx), utilSpan: utiltrace.FromContext(ctx)}`).
The trust boundary: an axiom, `Proof/k8s_io/component_base/tracing/SpanFromContext.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev tracing.SpanFromContext.spec : Prop :=
  ∀ (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_base.tracing }}
    (App (Val (@! k8s_io.component_base.tracing.SpanFromContext)) (Val #ctx))
  {{ (sp : Loc), RET #sp; ⌜sp ≠ null⌝ }}

end spec

end EtcdGrove
end Perennial
