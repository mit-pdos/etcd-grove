/-
Proof of `Spec/k8s_io/kubernetes/pkg/controller/ExpKeyFunc.lean`. Lean-first.
-/
module

public import Spec.k8s_io.kubernetes.pkg.controller.ExpKeyFunc

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode k8s_io.kubernetes.pkg.controller

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.controller.Assumptions]

theorem ExpKeyFunc.wp_proof : ExpKeyFunc.spec (GF := GF) (hG := hG) := by
  intro e k
  wp_start_folded as #Hk
  unfold expKeyFn
  wp_pures
  wp_auto
  iapply HΦ; itrivial

end proof

end dsctl
end EtcdGrove
end Perennial
