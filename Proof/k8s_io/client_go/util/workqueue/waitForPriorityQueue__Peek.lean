/-
Proof of `Spec/k8s_io/client_go/util/workqueue/waitForPriorityQueue__Peek.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.waitForPriorityQueue__Peek

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

theorem waitForPriorityQueue.Peek.wp_proof : waitForPriorityQueue.Peek.spec (GF := GF) (hG := hG) := by
  intro K T _ s a ws
  wp_start as Hq
  iunfold wqAt at Hq
  icases Hq with ⟨Hs, Hcap, Hits⟩
  ihave %Hlen := ownSlice_len s _ _ $$ Hs
  simp only [List.length_map, List.length_cons] at Hlen
  wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s.len by word)]
  wp_apply wp_load_slice_index s (sint.Z (W64 0)) ((a :: ws).map Prod.fst) _ a.1 (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rfl
  iapply HΦ
  iunfold wqAt
  iframe

end proof

end workqueue
end EtcdGrove
end Perennial
