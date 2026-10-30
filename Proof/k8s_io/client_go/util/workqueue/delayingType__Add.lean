/-
Proof of `Spec/k8s_io/client_go/util/workqueue/delayingType__Add.lean`. Lean-first: the method `delayingType`
promotes from its embedded `TypedInterface` (a wrapper calling `q.TypedInterface.Add`), as `Typed.Add` on the typed queue
in it.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.delayingType__Add
public import Spec.k8s_io.client_go.util.workqueue.Typed__Add

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

theorem delayingType.Add.wp_proof
    (wp_Add : Typed.Add.spec (GF := GF) (hG := hG)) :
    delayingType.Add.spec (GF := GF) (hG := hG) := by
  intro K T _ q γ k
  wp_start as #Hq
  iNamed Hq
  wp_auto
  wp_apply wp_Add $$ [$Htyped]
  iapply HΦ; itrivial

end proof

end workqueue
end EtcdGrove
end Perennial
