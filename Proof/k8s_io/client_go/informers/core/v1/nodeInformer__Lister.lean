/-
Proof of `Spec/k8s_io/client_go/informers/core/v1/nodeInformer__Lister.lean`: a glue proof (the DaemonSet autoverify run,
track A), over its callees' specs.
-/
module

public import Spec.k8s_io.client_go.informers.core.v1.nodeInformer__Lister
public import Spec.k8s_io.client_go.informers.core.v1.nodeInformer__Informer
public import Spec.k8s_io.client_go.listers.core.v1.NewNodeLister

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
theorem nodeInformer.Lister.wp_proof
    (wp_Informer : coreinformers.nodeInformer.Informer.spec (GF := GF) (hG := hG))
    (wp_NewNodeLister : corelisters.NewNodeLister.spec (GF := GF) (hG := hG)) :
    nodeInformer.Lister.spec (GF := GF) (hG := hG) := by
  intro l f γF γa cfg Fams
  wp_start as ⟨#Hl, #Hf⟩
  wp_auto
  wp_apply (wp_Informer l f γF γa cfg Fams) $$ [$Hl $Hf] as %x #Hx
  iunfold facInfOut at Hx
  icases Hx with ⟨%I, #HfI, #Hinf, -⟩
  iunfold isInformer at Hinf
  icases Hinf with ⟨%i, %Hxi, -, -, -, #HgetIdx, -⟩
  subst Hxi
  wp_auto
  wp_apply HgetIdx
  (try wp_auto)
  wp_apply (wp_NewNodeLister (storeVal I)) as %ll %res Hll
  iapply HΦ
  iexists I
  iframe #
  unfold listers.riVal storeVal
  iexact Hll

end proof

end coreinformers
end EtcdGrove
end Perennial
