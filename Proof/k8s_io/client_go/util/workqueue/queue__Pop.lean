/-
Proof of `Spec/k8s_io/client_go/util/workqueue/queue__Pop.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.queue__Pop

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

theorem queue.Pop.wp_proof : queue.Pop.spec (GF := GF) (hG := hG) := by
  intro K T _ l k xs
  wp_start as Hq
  iunfold ownFifo at Hq
  icases Hq with ⟨%s, Hl, Hs, Hcap⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
  simp only [List.length_cons] at Hlen
  wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s.len by word)]
  wp_apply wp_load_slice_index s (sint.Z (W64 0)) (k :: xs) _ k (by decide) $$ [Hs] as Hs
  · iframe; ipureintro; rfl
  wp_alloc_anon
  wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z s.len by word)]
  wp_apply wp_store_slice_index s (sint.Z (W64 0)) (k :: xs) (zero_val K) $$ [Hs] as Hs
  · iframe; ipureintro; simp only [List.length_cons]; word
  rw [if_pos (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z s.len ∧ sint.Z s.len ≤ sint.Z s.cap by word)]
  icases (ownSlice_slice (W64 1) s.len s (DFrac.own 1) (zero_val K :: xs)
    ⟨by word, by word, by word⟩).1 $$ Hs with ⟨-, Hs, -⟩
  ihave Hcap := (ownSliceCap_slice (V := K) s (W64 1) (DFrac.own 1) ⟨by word, by word, by word⟩).1 $$ Hcap
  wp_auto
  iapply HΦ
  iunfold ownFifo
  iexists _
  iframe
  have h1 : sint.nat (W64 1) = 1 := by decide
  have h2 : sint.nat s.len = xs.length + 1 := by omega
  rw [h1, h2]
  simp [subslice]
  iexact Hs

end proof

end workqueue
end EtcdGrove
end Perennial
