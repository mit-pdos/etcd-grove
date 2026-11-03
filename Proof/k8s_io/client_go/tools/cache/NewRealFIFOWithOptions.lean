/-
Proof of `Spec/k8s_io/client_go/tools/cache/NewRealFIFOWithOptions.lean`: a `sorry` stub (Stage 3 of the DaemonSet autoverify run,
track A), its hypotheses the specs of the callees its Go body calls.
Missing callee specs (next round): `newFIFOMetrics` (the no-op metrics: `gaugeOk`, `obsOk`),
`sync.NewCond`, the channel `make` (Perennial's).
-/
module

public import Spec.k8s_io.client_go.tools.cache.NewRealFIFOWithOptions
public import Spec.k8s_io.client_go.tools.cache.InformerNameAndResource__Name_ptr
public import Spec.k8s_io.klog.v2.Background

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cache

open Iris Iris.BI apimodel cache informer k8s_io.client_go.tools.cache

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

theorem NewRealFIFOWithOptions.wp_proof
    (wp_Background : klog.Background.spec (GF := GF) (hG := hG))
    (wp_Name : cache.InformerNameAndResource.Name_ptr.spec (GF := GF) (hG := hG)) :
    NewRealFIFOWithOptions.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end cache
end EtcdGrove
end Perennial
