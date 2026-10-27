/-
The trust boundary of component-base's `HistogramVec.WithContext` (see its spec).
-/
module

public import Spec.k8s_io.component_base.metrics.HistogramVec__WithContext

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The trust boundary (see the spec's file header). -/
axiom kmetrics.HistogramVec.WithContext.wp_proof :
  kmetrics.HistogramVec.WithContext.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
