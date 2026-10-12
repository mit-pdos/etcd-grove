/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.applyCompares
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.applyCompare

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.server.v3.storage.mvcc go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.applyCompares.wp_proof
    (hCmp : txn.applyCompare.spec (GF := GF) (hG := hG)) :
    txn.applyCompares.spec (GF := GF) (hG := hG) := by
  intro mw s γ log rev sl cps cms
  wp_start as ⟨Htx, #Hsl, #Hcs⟩
  iunfold txn.comparesIs at Hcs
  icases Hcs with ⟨%Hlen, #Hcs⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  ihave IH : (∃ (n : w64) (cv : Loc), "i" ∷ i_ptr ↦ n ∗ "c" ∷ c_ptr ↦ cv ∗
      "Htx" ∷ mvcc.isTxnRead mw s γ log rev ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len ∧
        ∀ j < sint.nat n, ∀ cm, cms[j]? = some cm → cmpHolds (mvcc.stateAfter log) cm = true⌝ :
      IProp GF) $$ [i c Htx]
  · iexists W64 0, _
    iframe
    ipureintro; refine ⟨by decide, Hsll.2, fun j hj => by simp at hj; omega⟩
  wp_for IH
  wp_if_destruct
  · obtain ⟨hn0, hnl, hall⟩ := Hn
    have hlt : sint.nat n < cps.length := by have := Hsll.1; word
    list_elem cps (sint.nat n) as p
    list_elem cms (sint.nat n) as cm
    simp only [show (0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len) from ⟨hn0, Hif⟩, _root_.and_self, ite_true]
    wp_apply wp_load_slice_index sl (sint.Z n) cps DFrac.discard p hn0 $$ [Hsl] as -
    · iframe Hsl; ipureintro; exact Hp_lookup
    ihave #Hp := Hcs $$ %(sint.nat n) %p %cm %Hp_lookup %Hcm_lookup
    wp_apply (hCmp mw s γ log rev p cm) $$ [$Htx $Hp] as Htx
    cases hb : cmpHolds (mvcc.stateAfter log) cm
    · wp_auto
      wp_for_post
      have : cms.all (cmpHolds (mvcc.stateAfter log)) = false := by
        rw [Bool.eq_false_iff]
        intro h
        rw [List.all_eq_true] at h
        rw [h cm (List.mem_of_getElem? Hcm_lookup)] at hb
        cases hb
      rw [this]
      iapply HΦ
      iframe Htx
    · wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, p
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      intro j hj w hw
      have hsn : sint.nat (n + W64 1) = sint.nat n + 1 := by word
      rw [hsn] at hj
      by_cases hjn : j = sint.nat n
      · subst hjn; rw [Hcm_lookup] at hw; cases hw; exact hb
      · exact hall j (by omega) w hw
  · obtain ⟨hn0, hnl, hall⟩ := Hn
    have : cms.all (cmpHolds (mvcc.stateAfter log)) = true := by
      rw [List.all_eq_true]
      intro w hw
      obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem hw
      exact hall j (by have := Hsll.1; word) w (by rw [List.getElem?_eq_getElem hj, hjw])
    rw [this]
    iapply HΦ
    iframe Htx

end proof

end EtcdGrove
end Perennial
