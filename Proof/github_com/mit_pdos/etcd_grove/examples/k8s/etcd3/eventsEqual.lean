module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.eventsEqual

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel WEvent change)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem eventsEqual.wp_proof : eventsEqual.spec (GF := GF) (hG := hG) := by
  intro a b ea eb
  wp_start as ⟨#Ha, #Hb⟩
  unfold wevsOwn
  icases Ha with ⟨%wa, #Hak, %Hea⟩
  icases Hb with ⟨%wb, #Hbk, %Heb⟩
  subst Hea Heb
  ihave %Hla := ownSlice_len $$ Hak
  ihave %Hlb := ownSlice_len $$ Hbk
  wp_auto
  wp_if_destruct
  · have Heq := Hif; clear Hif
    rename_i iu_ptr
    irename : (iu_ptr ↦ zero_val w64 : IProp GF) => Hiu
    ihave HI : (∃ (i j : w64),
        "i" ∷ i_ptr ↦ i ∗ "Hiu" ∷ iu_ptr ↦ j ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z a.len ∧
          (wa.map wevOf).take (sint.nat i) = (wb.map wevOf).take (sint.nat i)⌝ : IProp GF) $$ [i Hiu]
    · iexists W64 0, _
      iframe
      ipureintro; refine ⟨by word, by word, rfl⟩
    wp_for HI
    wp_if_destruct
    · have Hb' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z a.len := ⟨Hi.1, Hif⟩
      have Hb2' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z b.len := by rw [← Heq]; exact Hb'
      list_elem wa (sint.nat i) as w
      list_elem wb (sint.nat i) as w2
      simp only [Hb', _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index a (sint.Z i) wa _ w Hi.1 $$ [Hak] as -
      · isplit
        · iexact Hak
        · ipureintro; exact Hw_lookup
      icases ownSlice_elem_acc (sint.Z i) w a _ wa Hi.1 (by simpa [sint.nat] using Hw_lookup)
        $$ Hak with ⟨#Hva, -⟩
      icases ownSlice_elem_acc (sint.Z i) w2 b _ wb Hi.1 (by simpa [sint.nat] using Hw2_lookup)
        $$ Hbk with ⟨#Hvb, -⟩
      iStructNamedSuffix Hva "_a"
      iStructNamedSuffix Hvb "_b"
      iterate 4 ((try simp only [Hb', Hb2', _root_.and_self, ↓reduceIte]); (try wp_auto))
      have hla : (wa.map wevOf)[sint.nat i]? = some (wevOf w) := by simp [Hw_lookup]
      have hlb : (wb.map wevOf)[sint.nat i]? = some (wevOf w2) := by simp [Hw2_lookup]
      wp_if_destruct
      · have hT := Hif; clear Hif
        iterate 3 ((try simp only [Hb', Hb2', _root_.and_self, ↓reduceIte]); (try wp_auto))
        repeat' wp_if_destruct
        all_goals first
          | (have ho : w.Obj' = w2.Obj' := by rw [Obj_eq_iff]; and_intros <;> assumption
             wp_for_post
             iframe
             iexists i + W64 1, _
             iframe
             ipureintro
             refine ⟨by word, by word, ?_⟩
             have hw : wevOf w = wevOf w2 := by simp only [wevOf, hT, ho]
             rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one,
               List.take_add_one, Hi.2.2, hla, hlb, hw])
          | (have hne : ¬ w.Obj' = w2.Obj' := fun h => by rw [Obj_eq_iff] at h; simp_all
             wp_for_post
             rw [evsEqL_false_of _ _ _ _ _ hla hlb (wevOf_ne_obj w w2 hne)]
             iapply HΦ; itrivial)
      · (try wp_auto)
        wp_for_post
        rw [evsEqL_false_of _ _ _ _ _ hla hlb (wevOf_ne_type w w2 Hif)]
        iapply HΦ; itrivial
    · have h1 : wa.length = sint.nat i := by word
      have h2 : wb.length = sint.nat i := by rw [Hlb.1, ← Heq]; word
      have heq : wa.map wevOf = wb.map wevOf := by
        have := Hi.2.2
        rw [List.take_of_length_le (by simp [h1]), List.take_of_length_le (by simp [h2])] at this
        exact this
      rw [heq, show evsEqL (wb.map wevOf) (wb.map wevOf) = true by simp [evsEqL]]
      iapply HΦ; itrivial
  · have hne : evsEqL (wa.map wevOf) (wb.map wevOf) = false := by
      cases h : evsEqL (wa.map wevOf) (wb.map wevOf)
      · rfl
      · exfalso; apply Hif
        have := ((evsEqL_iff _ _).1 h).1
        simp only [List.length_map] at this
        word
    rw [hne]
    iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
