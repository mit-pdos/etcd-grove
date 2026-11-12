/-
Proof of `Spec/k8s_io/client_go/util/workqueue/delayingType__Get.lean`. Lean-first: the method `delayingType`
promotes from its embedded `TypedInterface` (a wrapper calling `q.TypedInterface.Get`), as `Typed.Get` on the typed queue
in it.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.delayingType__Get
public import Spec.k8s_io.client_go.util.workqueue.Typed__Get

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

theorem delayingType.Get.wp_proof
    (wp_Get : Typed.Get.spec (GF := GF) (hG := hG)) :
    delayingType.Get.spec (GF := GF) (hG := hG) := by
  intro K T _ q γ
  wp_start as #Hq
  iNamed Hq
  wp_auto
  wp_apply wp_Get $$ [$Htyped] as %k %sd HR
  iapply HΦ; iexact HR

end proof

end workqueue
end EtcdGrove
end Perennial
