/- Lean-first (no Rocq counterpart). The proof of `appendEnts`. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.appendEnts
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.RefLemmas

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

theorem appendEnts.wp_proof : appendEnts.spec (GF := GF) (hG := hG) := by
  intro b old es olds ess
  wp_start as ⟨#Ho, #He⟩
  ihave %Holen := ownSlice_len $$ Ho
  ihave %Helen := ownSlice_len $$ He
  ihave %Howf := ownSlice_wf $$ Ho
  wp_auto
  ihave HI : (∃ (st : w64),
      "start" ∷ start_ptr ↦ st ∗ "es" ∷ es_ptr ↦ es ∗ "b" ∷ b_ptr ↦ b ∗
      "%Hst" ∷ ⌜0 ≤ sint.Z st ∧ sint.Z st ≤ sint.Z es.len⌝ : IProp GF) $$ [start es b]
  · iexists W64 0
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  by_cases hlt : sint.Z st < sint.Z es.len
  · have hil : sint.nat st < ess.length := by
      have : sint.nat st < sint.nat es.len := by word
      omega
    obtain ⟨x, Hx⟩ : ∃ x, ess[sint.nat st]? = some x := ⟨_, List.getElem?_eq_getElem hil⟩
    have hb : 0 ≤ sint.Z st ∧ sint.Z st < sint.Z es.len := ⟨Hst.1, hlt⟩
    icases ownSlice_elem_acc (sint.Z st) x es DFrac.discard ess Hst.1 (by simpa [sint.nat] using Hx) $$ He
      with ⟨Hx, -⟩
    iStructNamed Hx
    simp only [hlt, decide_true]
    wp_auto
    repeat (simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
    by_cases hxb : uint.Z x.index' ≤ uint.Z b
    · rw [if_pos (by simp [hxb])]
      wp_auto
      wp_for_post
      iframe
      iexists st + W64 1
      iframe
      ipureintro; constructor <;> word
    · rw [if_neg (by simp [hxb, val_false_ne_true]), if_pos (by simp [hxb])]
      wp_auto
      have hne : st ≠ es.len := by intro h'; subst h'; omega
      simp only [hne, decide_false]
      wp_auto
      repeat (simp only [hb, _root_.and_self, ↓reduceIte]; try wp_auto)
      wp_join iprop(∃ (kk : w64), k_ptr ↦ kk ∗ old_ptr ↦ old ∗ ⌜uint.nat kk ≤ olds.length⌝)
        at next with [k old] as ⟨%kk, k, old, %Hkk⟩
      · wp_if_destruct
        · wp_join_done
          iexists _
          iframe
          ipureintro; word
        · wp_join_done
          iexists _
          iframe
          ipureintro; word
      wp_apply +noauto (wp_slice_make2 (V := TEnt) (W64 0)) as %o0 ⟨Ho0, Ho0cap⟩
      · ipureintro; word
      simp only [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero]
      wp_auto
      ihave HJ : (∃ (i : w64) (o : GoSlice) (xs : List TEnt),
          "i" ∷ i_ptr ↦ i ∗ "out" ∷ out_ptr ↦ o ∗ "Hout" ∷ o ↦* xs ∗
          "Hcap" ∷ ownSliceCap TEnt o (DFrac.own 1) ∗ "old" ∷ old_ptr ↦ old ∗ "k" ∷ k_ptr ↦ kk ∗
          "%Hxs" ∷ ⌜∀ e ∈ xs, e ∈ olds ∨ e ∈ ess⌝ ∗
          "%Hi" ∷ ⌜uint.nat i ≤ uint.nat kk⌝ : IProp GF) $$ [i out Ho0 Ho0cap old k]
      · iexists W64 0, o0, []
        iframe
        ipureintro; constructor
        · intro e he; simp at he
        · word
      wp_for HJ
      by_cases hik : uint.Z i < uint.Z kk
      · rw [if_pos (by simp [hik])]
        have hil : uint.nat i < olds.length := by word
        obtain ⟨y, Hy⟩ : ∃ y, olds[uint.nat i]? = some y := ⟨_, List.getElem?_eq_getElem hil⟩
        wp_auto
        have hsi : sint.Z i = uint.Z i := by word
        have hb2 : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z old.len := by constructor <;> word
        simp only [hb2, _root_.and_self, ↓reduceIte]
        icases ownSlice_elem_acc (sint.Z i) y old DFrac.discard olds hb2.1
          (by rw [show (sint.Z i).toNat = uint.nat i by word]; exact Hy) $$ Ho with ⟨Hy, -⟩
        wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %ysl ⟨Hysl, -⟩
        wp_apply wp_slice_append $$ [$Hout $Hcap $Hysl] as %o' ⟨Hout, Hcap, -⟩
        wp_for_post
        iframe
        iexists i + W64 1, o', xs ++ [y]
        iframe
        ipureintro; constructor
        · intro e he
          rw [List.mem_append] at he
          rcases he with he | he
          · exact Hxs e he
          · simp at he; subst he; exact Or.inl (List.mem_of_getElem? Hy)
        · word
      · rw [if_neg (by simp [hik]), if_neg (by simp [hik])]
        wp_auto
        ihave HK : (∃ (i2 : w64) (o : GoSlice) (xs : List TEnt),
            "i" ∷ i_ptr ↦ i2 ∗ "out" ∷ out_ptr ↦ o ∗ "Hout" ∷ o ↦* xs ∗
            "Hcap" ∷ ownSliceCap TEnt o (DFrac.own 1) ∗ "es" ∷ es_ptr ↦ es ∗
            "%Hxs" ∷ ⌜∀ e ∈ xs, e ∈ olds ∨ e ∈ ess⌝ ∗
            "%Hi" ∷ ⌜0 ≤ sint.Z i2 ∧ sint.Z i2 ≤ sint.Z es.len⌝ : IProp GF) $$ [i out Hout Hcap es]
        · iexists st, o, xs
          iframe
          ipureintro; exact ⟨Hxs, by word, by word⟩
        wp_for HK
        by_cases hie : sint.Z i2 < sint.Z es.len
        · rw [if_pos (by simp [hie])]
          have hil : sint.nat i2 < ess.length := by
            have : sint.nat i2 < sint.nat es.len := by word
            omega
          obtain ⟨y, Hy⟩ : ∃ y, ess[sint.nat i2]? = some y := ⟨_, List.getElem?_eq_getElem hil⟩
          have hb3 : 0 ≤ sint.Z i2 ∧ sint.Z i2 < sint.Z es.len := ⟨Hi.1, hie⟩
          wp_auto
          simp only [hb3, _root_.and_self, ↓reduceIte]
          icases ownSlice_elem_acc (sint.Z i2) y es DFrac.discard ess hb3.1
            (by simpa [sint.nat] using Hy) $$ He with ⟨Hy, -⟩
          wp_auto
          wp_apply wp_slice_literal
          isplitr
          · ipureintro; rfl
          iintro %ysl ⟨Hysl, -⟩
          wp_apply wp_slice_append $$ [$Hout $Hcap $Hysl] as %o' ⟨Hout, Hcap, -⟩
          wp_for_post
          iframe
          iexists i2 + W64 1, o', xs ++ [y]
          iframe
          ipureintro; constructor
          · intro e he
            rw [List.mem_append] at he
            rcases he with he | he
            · exact Hxs e he
            · simp at he; subst he; exact Or.inr (List.mem_of_getElem? Hy)
          · constructor <;> word
        · rw [if_neg (by simp [hie]), if_neg (by simp [hie])]
          ipersist Hout
          wp_auto
          iapply HΦ
          iexists xs
          isplitl []
          · iexact Hout
          ipureintro; exact Hxs
  · simp only [hlt, decide_false]
    wp_auto
    rw [if_neg (by simp [val_false_ne_true]), if_pos (by simp)]
    have hst : st = es.len := by word
    subst hst
    wp_auto
    iapply HΦ
    iexists olds
    isplitl []
    · iexact Ho
    ipureintro; intro e he; exact Or.inl he

end proof

end etcd_wal
end EtcdGrove
end Perennial
