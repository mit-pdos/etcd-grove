/-
Proof of `Spec/k8s_io/client_go/util/workqueue/delayingType__ShuttingDown.lean`. Lean-first: the method `delayingType`
promotes from its embedded `TypedInterface` (a wrapper calling `q.TypedInterface.ShuttingDown`), as `Typed.ShuttingDown` on the typed queue
in it.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.delayingType__ShuttingDown
public import Spec.k8s_io.client_go.util.workqueue.Typed__ShuttingDown

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

theorem delayingType.ShuttingDown.wp_proof
    (wp_ShuttingDown : Typed.ShuttingDown.spec (GF := GF) (hG := hG)) :
    delayingType.ShuttingDown.spec (GF := GF) (hG := hG) := by
  intro K T _ q γ
  wp_start as #Hq
  iNamed Hq
  wp_auto
  wp_apply wp_ShuttingDown $$ [$Htyped] as %b HR
  iapply HΦ; iexact HR

end proof

end workqueue
end EtcdGrove
end Perennial
