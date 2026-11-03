/-
Proof of `Spec/k8s_io/client_go/tools/cache/InformerName__WithResource.lean`: a `sorry` stub (Stage 3 of the DaemonSet autoverify run,
track A), its hypotheses the specs of the callees its Go body calls.
Its body (the `nil` branch) calls nothing. Note: `InformerName` is names-only (gap D5), so
the proof needs its method's unfolding: to check against the translation.
-/
module

public import Spec.k8s_io.client_go.tools.cache.InformerName__WithResource

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
variable [ctx_sem : _root_.Perennial.context.Assumptions]

theorem InformerName.WithResource.wp_proof :
    InformerName.WithResource.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end cache
end EtcdGrove
end Perennial
