/-
Proof of `Spec/k8s_io/client_go/util/workqueue/delayingType__Done.lean`. Lean-first: the method `delayingType`
promotes from its embedded `TypedInterface` (a wrapper calling `q.TypedInterface.Done`), as `Typed.Done` on the typed queue
in it.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.delayingType__Done
public import Spec.k8s_io.client_go.util.workqueue.Typed__Done

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

theorem delayingType.Done.wp_proof
    (wp_Done : Typed.Done.spec (GF := GF) (hG := hG)) :
    delayingType.Done.spec (GF := GF) (hG := hG) := by
  intro K T _ q γ k
  wp_start as ⟨#Hq, Htok⟩
  iNamed Hq
  wp_auto
  wp_apply wp_Done $$ [$Htyped $Htok]
  iapply HΦ; itrivial

end proof

end workqueue
end EtcdGrove
end Perennial
