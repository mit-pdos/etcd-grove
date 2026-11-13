/- Lean-first (no Rocq counterpart). The proof of `opEq`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.opEq
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.hsEq
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.entEq

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem opEq.wp_proof (wp_hsEq : hsEq.spec (GF := GF) (hG := hG))
    (wp_entEq : entEq.spec (GF := GF) (hG := hG)) :
    opEq.spec (GF := GF) (hG := hG) := by
  intro va vb oa ob
  wp_start as ⟨Ha, Hb⟩
  iunfold opRep at Ha Hb
  icases Ha with ⟨%Haf, #Hae⟩
  icases Hb with ⟨%Hbf, #Hbe⟩
  obtain ⟨has, hah, hai, hat⟩ := Haf
  obtain ⟨hbs, hbh, hbi, hbt⟩ := Hbf
  ihave %Hal := ownSlice_len $$ Hae
  ihave %Hbl := ownSlice_len $$ Hbe
  ihave HΦ := ret_gen _ _ _ $$ HΦ
  wp_auto
  wp_if_destruct
  · wp_if_destruct
    · wp_if_destruct
      · wp_apply wp_hsEq
        wp_if_destruct
        · wp_if_destruct
          · have hleq := Hif
            have hlen : oa.ents.length = ob.ents.length := by rw [Hal.1, Hbl.1, Hif]
            ihave HI : (∃ (j : w64), "i" ∷ i_ptr ↦ j ∗
                "%Ht" ∷ ⌜oa.ents.take (sint.nat j) = ob.ents.take (sint.nat j)⌝ ∗
                "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z va.ents'.len⌝ : IProp GF) $$ [i]
            · iexists W64 0
              iframe
              isplit
              · ipureintro; rw [show sint.nat (W64 0) = 0 from rfl]; simp
              · ipureintro; constructor <;> word
            wp_for HI
            by_cases hlt : sint.Z j < sint.Z va.ents'.len
            · rw [if_pos (by simp [hlt])]
              have hjl : sint.nat j < oa.ents.length := by
                have : sint.nat j < sint.nat va.ents'.len := by word
                omega
              obtain ⟨x, Hx⟩ : ∃ x, oa.ents[sint.nat j]? = some x := ⟨_, List.getElem?_eq_getElem hjl⟩
              obtain ⟨y, Hy⟩ : ∃ y, ob.ents[sint.nat j]? = some y :=
                ⟨_, List.getElem?_eq_getElem (by omega)⟩
              have hba : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z va.ents'.len := ⟨Hj.1, hlt⟩
              have hbb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z vb.ents'.len := ⟨Hj.1, by rw [← hleq]; exact hlt⟩
              icases ownSlice_elem_acc (sint.Z j) x va.ents' DFrac.discard oa.ents Hj.1
                (by simpa [sint.nat] using Hx) $$ Hae with ⟨Hxv, -⟩
              icases ownSlice_elem_acc (sint.Z j) y vb.ents' DFrac.discard ob.ents Hj.1
                (by simpa [sint.nat] using Hy) $$ Hbe with ⟨Hyv, -⟩
              wp_auto
              repeat (simp only [hba, hbb, _root_.and_self, ↓reduceIte]; try wp_auto)
              wp_apply wp_entEq
              wp_if_destruct
              · wp_for_post
                iframe
                iexists j + W64 1
                iframe
                have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
                rw [hj1]
                isplit
                · ipureintro; rw [← Hif] at Hy; exact list_take_succ_eq Hx Hy Ht
                · ipureintro; constructor <;> word
              · wp_for_post
                iapply HΦ
                isplitl []
                · ipureintro; rw [eq_comm, decide_eq_false_iff_not]; intro hc; subst hc
                  rw [Hx] at Hy; exact Hif (Option.some.inj Hy)
                · itrivial
            · simp only [hlt, decide_false, Bool.false_eq_true, ↓reduceIte]
              have hjn : sint.nat j = oa.ents.length := by
                have : sint.nat j = sint.nat va.ents'.len := by word
                omega
              rw [hjn, List.take_length, hlen, List.take_length] at Ht
              wp_auto
              wp_end
              ipureintro
              rw [eq_comm, decide_eq_true_iff]
              cases oa; cases ob
              simp_all
          · iapply HΦ
            isplitl []
            · ipureintro; rw [eq_comm, decide_eq_false_iff_not]; intro hc; subst hc
              apply Hif; have h1 := Hal.1; have h2 := Hbl.1; word
            · itrivial
        · iapply HΦ
          isplitl []
          · ipureintro; rw [eq_comm, decide_eq_false_iff_not]; intro hc; subst hc; simp_all
          · itrivial
      · iapply HΦ
        isplitl []
        · ipureintro; rw [eq_comm, decide_eq_false_iff_not]; intro hc; subst hc; simp_all
        · itrivial
    · iapply HΦ
      isplitl []
      · ipureintro; rw [eq_comm, decide_eq_false_iff_not]; intro hc; subst hc; simp_all
      · itrivial
  · iapply HΦ
    isplitl []
    · ipureintro; rw [eq_comm, decide_eq_false_iff_not]; intro hc; subst hc; simp_all
    · itrivial

end proof

end etcd_wal
end EtcdGrove
end Perennial
