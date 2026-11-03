/-
Proof of `Spec/k8s_io/client_go/informers/core/group__V1.lean`: a `sorry` stub (Stage 3 of the DaemonSet autoverify run,
track A), its hypotheses the specs of the callees its Go body calls.
-/
module

public import Spec.k8s_io.client_go.informers.core.group__V1
public import Spec.k8s_io.client_go.informers.core.v1.New

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace informerscore

open Iris Iris.BI apimodel cache informer informers

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.informers.core.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

theorem group.V1.wp_proof
    (wp_New : coreinformers.New.spec (GF := GF) (hG := hG)) :
    group.V1.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end informerscore
end EtcdGrove
end Perennial
