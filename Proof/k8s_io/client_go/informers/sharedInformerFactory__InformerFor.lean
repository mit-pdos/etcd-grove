/-
Proof of `Spec/k8s_io/client_go/informers/sharedInformerFactory__InformerFor.lean`: a `sorry` stub (Stage 3 of the DaemonSet autoverify run,
track A), its hypotheses the specs of the callees its Go body calls.
-/
module

public import Spec.k8s_io.client_go.informers.sharedInformerFactory__InformerFor
public import Spec.reflect.TypeOf

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace informers

open Iris Iris.BI apimodel cache informer informers

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.informers.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

theorem sharedInformerFactory.InformerFor.wp_proof
    (wp_TypeOf : reflect.TypeOf.spec (GF := GF) (hG := hG)) :
    sharedInformerFactory.InformerFor.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end informers
end EtcdGrove
end Perennial
