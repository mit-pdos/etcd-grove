/-
The trust boundary: `prometheus.GaugeVec.WithLabelValues` (`prometheus` is names-only).
-/
module

public import Spec.github_com.prometheus.client_golang.prometheus.GaugeVec__WithLabelValues

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

axiom prometheus.GaugeVec.WithLabelValues.wp_proof : prometheus.GaugeVec.WithLabelValues.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
