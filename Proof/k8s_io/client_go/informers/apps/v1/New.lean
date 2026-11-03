/-
Proof of `Spec/k8s_io/client_go/informers/apps/v1/New.lean`: a glue proof (the DaemonSet autoverify run,
track A).
Its body calls nothing (a struct literal).
-/
module

public import Spec.k8s_io.client_go.informers.apps.v1.New

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
theorem New.wp_proof :
    New.spec (GF := GF) (hG := hG) := by
  intro f
  wp_start
  wp_auto
  wp_alloc v as Hv
  iStructNamed Hv
  ipersist factory
  ipersist namespace'
  ipersist tweakListOptions
  (try wp_auto)
  iapply HΦ
  unfold facRefAt
  iframe #

end proof

end appsinformers
end EtcdGrove
end Perennial
