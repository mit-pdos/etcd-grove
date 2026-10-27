/-
Proof of `Spec/k8s_io/client_go/util/workqueue/waitForPriorityQueue__Less.lean`. Lean-first.
-/
module

public import Spec.k8s_io.client_go.util.workqueue.waitForPriorityQueue__Less

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

theorem waitForPriorityQueue.Less.wp_proof : waitForPriorityQueue.Less.spec (GF := GF) (hG := hG) := by
  intro K T _ s ws i j hi0 hi1 hj0 hj1
  wp_start as Hq
  iunfold wqAt at Hq
  icases Hq with ⟨Hs, Hcap, Hits⟩
  ihave %Hlen := ownSlice_len s _ _ $$ Hs
  simp only [List.length_map] at Hlen
  have hj : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := ⟨hj0, by word⟩
  have hi : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z s.len := ⟨hi0, by word⟩
  obtain ⟨xj, hxj⟩ : ∃ x, ws[(sint.Z j).toNat]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨xi, hxi⟩ : ∃ x, ws[(sint.Z i).toNat]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  wp_auto
  simp only [hj, _root_.and_self, ite_true]
  wp_apply wp_load_slice_index s (sint.Z j) (ws.map Prod.fst) _ xj.1 hj0 $$ [Hs] as Hs
  · iframe; ipureintro; simp [hxj]
  icases (BigSepL.bigSepL_lookup_acc hxj).1 $$ Hits with ⟨Hxj, Hits⟩
  iunfold wfAt at Hxj
  icases Hxj with ⟨#Hid, ⟨%t, Ht⟩, Hix⟩
  wp_auto
  ihave Hits := Hits $$ [Hid Ht Hix]
  · iunfold wfAt; iframe Hid Hix; iexists t; iexact Ht
  rw [list_set_lookup_self ws (sint.Z j).toNat xj hxj]
  simp only [hi, _root_.and_self, ite_true]
  icases (BigSepL.bigSepL_lookup_acc hxi).1 $$ Hits with ⟨Hxi, Hits⟩
  iunfold wfAt at Hxi
  icases Hxi with ⟨#Hid', ⟨%t', Ht'⟩, Hix'⟩
  wp_apply wp_load_slice_index s (sint.Z i) (ws.map Prod.fst) _ xi.1 hi0 $$ [Hs] as Hs
  · iframe; ipureintro; simp [hxi]
  wp_apply Time.wp_ptr_Before_dq' $$ [$Ht'] as %b Ht'
  iapply HΦ
  ihave Hits := Hits $$ [Hid' Ht' Hix']
  · iunfold wfAt; iframe Hid' Hix'; iexists t'; iexact Ht'
  rw [list_set_lookup_self ws (sint.Z i).toNat xi hxi]
  iunfold wqAt
  iframe

end proof

end workqueue
end EtcdGrove
end Perennial
