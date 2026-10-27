/-
Proof of `Spec/k8s_io/client_go/util/workqueue/waitForPriorityQueue__Pop.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.waitForPriorityQueue__Pop

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

theorem waitForPriorityQueue.Pop.wp_proof : waitForPriorityQueue.Pop.spec (GF := GF) (hG := hG) := by
  intro K T _ pq s ws a
  wp_start as ⟨Hpq, Hq⟩
  iunfold wqAt at Hq
  icases Hq with ⟨Hs, Hcap, Hits⟩
  ihave %Hlen := ownSlice_len s _ _ $$ Hs
  ihave %Hcw := ownSliceCap_wf _ _ $$ Hcap
  simp only [List.length_map, List.length_append, List.length_singleton] at Hlen
  icases BigSepL.bigSepL_snoc.1 $$ Hits with ⟨Hits, Ha⟩
  wp_auto
  have hn1 : 0 ≤ sint.Z (s.len - W64 1) ∧ sint.Z (s.len - W64 1) < sint.Z s.len := by
    constructor <;> word
  rw [if_pos hn1]
  have hlast : (List.map Prod.fst (ws ++ [a]))[(sint.Z (s.len - W64 1)).toNat]? = some a.1 := by
    rw [show (sint.Z (s.len - W64 1)).toNat = ws.length by word]
    simp
  wp_apply wp_load_slice_index s (sint.Z (s.len - W64 1)) _ _ a.1 hn1.1 $$ [Hs] as Hs
  · iframe; ipureintro; exact hlast
  iunfold wfAt at Ha
  icases Ha with ⟨#Hid, Ht, Hix⟩
  wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (s.len - W64 1) ∧
    sint.Z (s.len - W64 1) ≤ sint.Z s.cap by word)]
  wp_auto
  icases (ownSlice_slice (W64 0) (s.len - W64 1) s (DFrac.own 1) (List.map Prod.fst (ws ++ [a]))
    ⟨by word, by word, by word⟩).1 $$ Hs with ⟨Hs0, Hs, Hs2⟩
  ihave Hcap := ownSlice_slice_absorb_capacity s _ (W64 0) (s.len - W64 1) ⟨by word, by word, by word⟩
    $$ [Hs2 Hcap]
  · iframe
  iapply HΦ
  isplitl [Hpq Hs Hcap Hits]
  · iexists _
    iframe Hpq
    iunfold wqAt
    iframe
    have h0 : sint.nat (W64 0) = 0 := rfl
    have h1 : sint.nat (s.len - W64 1) = ws.length := by word
    rw [h0, h1]
    simp [subslice]
    iexact Hs
  · iunfold wfAt
    iframe
    iframe #

end proof

end workqueue
end EtcdGrove
end Perennial
