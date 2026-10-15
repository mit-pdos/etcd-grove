/-
The trust boundary: `prometheus.HistogramVec.WithLabelValues` (metrics: the observer of a label set, whose `Observe` has no effect the model sees).
-/
module

public import Spec.github_com.prometheus.client_golang.prometheus.HistogramVec__WithLabelValues

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom prometheus.HistogramVec.WithLabelValues.wp_proof : prometheus.HistogramVec.WithLabelValues.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
