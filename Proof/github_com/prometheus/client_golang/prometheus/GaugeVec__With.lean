/-
The trust boundary: `(*prometheus.GaugeVec).With(labels)`: names-only (the server's `start` sets the cluster version gauge).
-/
module

public import Spec.github_com.prometheus.client_golang.prometheus.GaugeVec__With

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

axiom prometheus.GaugeVec.With.wp_proof : prometheus.GaugeVec.With.spec (GF := GF) (hG := hG)

end proof

end EtcdGrove
end Perennial
