/-
`span.End(logThreshold)` (names-only): a no-op for the store's results, on a span
(`tracing.isSpan`). Proved from it (`Proof/k8s_io/component_base/tracing/Span__End.lean`); until
2026-11-06 an axiom on any non-nil `*Span`, false: a program can allocate a `tracing.Span{}`, whose
nil `otelSpan` makes `End` panic (the fix of the tracing axioms,
`Proof/k8s_io/component_base/tracing/Defs.lean`; the user approved fixing axioms as needed).
Lean-first (no Rocq counterpart).
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
abbrev tracing.Span.End.spec : Prop :=
  ∀ (sp : Loc) (d : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_base.tracing ∗ tracing.isSpan sp }}
    (App (Val (sp @!! go.GoType.PointerType k8s_io.component_base.tracing.Span.ty @!! go!"End"))
      (Val #d))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
