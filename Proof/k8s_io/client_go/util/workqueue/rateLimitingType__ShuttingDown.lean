/-
Proof of `Spec/k8s_io/client_go/util/workqueue/rateLimitingType__ShuttingDown.lean`. Lean-first: the method `rateLimitingType`
promotes from its embedded `TypedDelayingInterface` (a wrapper calling `q.TypedDelayingInterface.ShuttingDown`), as `delayingType.ShuttingDown` on the delaying queue
in it.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.rateLimitingType__ShuttingDown
public import Spec.k8s_io.client_go.util.workqueue.delayingType__ShuttingDown

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

theorem rateLimitingType.ShuttingDown.wp_proof
    (wp_ShuttingDown : delayingType.ShuttingDown.spec (GF := GF) (hG := hG)) :
    rateLimitingType.ShuttingDown.spec (GF := GF) (hG := hG) := by
  intro K T _ q γ P
  wp_start as #Hq
  iunfold isRateLimitingQueue at Hq
  icases Hq with ⟨%dq, %rl, #Hdf, #Hd, #Hrlf, #Hrl⟩
  wp_auto
  wp_apply wp_ShuttingDown $$ [$Hd] as %b HR
  iapply HΦ; iexact HR

end proof

end workqueue
end EtcdGrove
end Perennial
