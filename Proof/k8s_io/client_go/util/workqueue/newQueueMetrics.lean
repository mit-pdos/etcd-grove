/-
Proof of `Spec/k8s_io/client_go/util/workqueue/newQueueMetrics.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.newQueueMetrics

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace workqueue

open Iris Iris.BI Iris.ProofMode k8s_io.client_go.util.workqueue

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.util.workqueue.Assumptions]

theorem newQueueMetrics.wp_proof : newQueueMetrics.spec (GF := GF) (hG := hG) := by
  intro K T _ mp name c Hpre
  wp_start
  wp_auto
  wp_func_call
  wp_call
  rcases Hpre with rfl | rfl
  · simp only [List.length_nil]
    wp_auto
    iapply HΦ; itrivial
  · by_cases hl : name.length < 2 ^ 63
    · rw [if_pos hl]
      wp_auto
      wp_if_destruct
      · iapply HΦ; itrivial
      · iapply HΦ; itrivial
    · rw [if_neg hl]
      wp_apply wp_AngelicExit

end proof

end workqueue
end EtcdGrove
end Perennial
