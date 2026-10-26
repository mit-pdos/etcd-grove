/-
`(*HistogramVec).WithContext(ctx)` (names-only; `k8s.io/component-base/metrics/histogram.go`):
`&HistogramVecWithContext{ctx: ctx, HistogramVec: v}`, whose `WithLabelValues` with values
accepted for the vector's labels returns an observer whose `Observe` returns (`histCtxOk`; a panic
otherwise, prometheus' `WithLabelValues`: `Proof/k8s_io/component_base/metrics/Defs.lean`). The
trust boundary: an axiom, `Proof/k8s_io/component_base/metrics/HistogramVec__WithContext.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.cacher.Base
public import Proof.k8s_io.component_base.metrics.Defs

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
abbrev kmetrics.HistogramVec.WithContext.spec : Prop :=
  ∀ (hv : Loc) (ls : List GoString) (ctx : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.component_base.metrics ∗ ⌜kmetrics.vecLabels hv ls⌝ }}
    (App (Val (hv @!! go.GoType.PointerType k8s_io.component_base.metrics.HistogramVec.ty @!!
      go!"WithContext")) (Val #ctx))
  {{ (vc : Loc), RET #vc; kmetrics.histCtxOk vc ls }}

end spec

end EtcdGrove
end Perennial
