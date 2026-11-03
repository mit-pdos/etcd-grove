/-
Proof of `Spec/k8s_io/client_go/informers/core/v1/podInformer__Informer.lean`: a glue proof (the DaemonSet autoverify run,
track A), over its callee's spec.
-/
module

public import Spec.k8s_io.client_go.informers.core.v1.podInformer__Informer
public import Spec.k8s_io.client_go.informers.core.v1.podInformer__TypedInformer

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace coreinformers

open Iris Iris.BI apimodel cache informer informers

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.informers.core.v1.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

open Iris.ProofMode in
theorem podInformer.Informer.wp_proof
    (wp_TypedInformer : coreinformers.podInformer.TypedInformer.spec (GF := GF) (hG := hG)) :
    podInformer.Informer.spec (GF := GF) (hG := hG) := by
  intro l f γF γa cfg Fams
  wp_start as ⟨#Hl, #Hf⟩
  wp_auto
  wp_apply (wp_TypedInformer l f γF γa cfg Fams) $$ [$Hl $Hf] as %x #Hx
  (try wp_auto)
  iapply HΦ
  iexact Hx

end proof

end coreinformers
end EtcdGrove
end Perennial
