/-
`span.End(logThreshold)` (names-only): a no-op for the store's results. The trust boundary: an axiom, `Proof/k8s_io/component_base/tracing/Span__End.lean`. Lean-first (no Rocq
counterpart).
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
abbrev tracing.Span.End.spec : Prop :=
  ∀ (sp : Loc) (d : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_base.tracing ∗ ⌜sp ≠ null⌝ }}
    (App (Val (sp @!! go.GoType.PointerType k8s_io.component_base.tracing.Span.ty @!! go!"End"))
      (Val #d))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
