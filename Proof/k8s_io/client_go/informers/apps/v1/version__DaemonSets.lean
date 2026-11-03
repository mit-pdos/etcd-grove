/-
Proof of `Spec/k8s_io/client_go/informers/apps/v1/version__DaemonSets.lean`: a glue proof (the DaemonSet autoverify run,
track A).
Its body calls nothing (a struct literal).
-/
module

public import Spec.k8s_io.client_go.informers.apps.v1.version__DaemonSets

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace appsinformers

open Iris Iris.BI apimodel cache informer informers

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.informers.apps.v1.Assumptions]
variable [cache_sem : k8s_io.client_go.tools.cache.Assumptions]
variable [ctx_sem : _root_.Perennial.context.Assumptions]

open Iris.ProofMode in
theorem version.DaemonSets.wp_proof :
    version.DaemonSets.spec (GF := GF) (hG := hG) := by
  intro v f
  wp_start as Hv
  iunfold facRefAt at Hv
  icases Hv with ⟨#Hf, #Hns, #Htw⟩
  wp_auto
  wp_alloc l as Hl
  iStructNamed Hl
  ipersist factory
  ipersist namespace'
  ipersist tweakListOptions
  (try wp_auto)
  iapply HΦ
  simp only [typedInfAt, typedInfStruct, facRefAt]
  iframe #

end proof

end appsinformers
end EtcdGrove
end Perennial
