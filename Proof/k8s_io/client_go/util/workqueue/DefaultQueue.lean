/-
Proof of `Spec/k8s_io/client_go/util/workqueue/DefaultQueue.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.DefaultQueue

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

theorem DefaultQueue.wp_proof : DefaultQueue.spec (GF := GF) (hG := hG) := by
  intro K T _
  wp_start
  wp_alloc_anon
  wp_auto
  wp_alloc_anon
  rename_i l
  wp_auto
  iapply HΦ
  iunfold ownFifo
  iexists slice.nil
  iframe
  isplitl
  · iapply ownSlice_nil
  iapply ownSliceCap_nil

end proof

end workqueue
end EtcdGrove
end Perennial
