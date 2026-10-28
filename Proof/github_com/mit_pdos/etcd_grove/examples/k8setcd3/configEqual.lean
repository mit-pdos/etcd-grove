/-
Lean-first (no Rocq counterpart).

The proof of `configEqual`: the stores, the lengths, then the loop's invariant is that the
pending inputs before the index are equal.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.configEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.storeEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.inputEqual

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8setcd3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

theorem configEqual.wp_proof (wp_storeEqual : storeEqual.spec (GF := GF) (hG := hG))
    (wp_inputEqual : inputEqual.spec (GF := GF) (hG := hG)) :
    configEqual.spec (GF := GF) (hG := hG) := by
  intro a b ga gb
  wp_start as ⟨#Ha, #Hb⟩
  unfold cfgOwn
  icases Ha with ⟨#Hast, #Hap⟩
  icases Hb with ⟨#Hbst, #Hbp⟩
  ihave %Hla := ownSlice_len $$ Hap
  ihave %Hlb := ownSlice_len $$ Hbp
  wp_auto
  wp_apply wp_storeEqual a.st' b.st' ga.st gb.st $$ [$Hast $Hbst]
  wp_if_destruct
  · have Hst := Hif; clear Hif
    wp_if_destruct
    · have Heq := Hif; clear Hif
      rename_i iu_ptr
      irename : (iu_ptr ↦ zero_val w64 : IProp GF) => Hiu
      ihave HI : (∃ (i j : w64),
          "i" ∷ i_ptr ↦ i ∗ "Hiu" ∷ iu_ptr ↦ j ∗
          "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z a.pend'.len ∧
            ga.pend.take (sint.nat i) = gb.pend.take (sint.nat i)⌝ : IProp GF) $$ [i Hiu]
      · iexists W64 0, _
        iframe
        ipureintro; refine ⟨by word, by word, rfl⟩
      wp_for HI
      wp_if_destruct
      · have Hb' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z a.pend'.len := ⟨Hi.1, Hif⟩
        have Hb2' : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z b.pend'.len := by rw [← Heq]; exact Hb'
        list_elem ga.pend (sint.nat i) as w
        list_elem gb.pend (sint.nat i) as w2
        simp only [Hb', _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index a.pend' (sint.Z i) ga.pend _ w Hi.1 $$ [Hap] as -
        · isplit
          · iexact Hap
          · ipureintro; exact Hw_lookup
        simp only [Hb', _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index a.pend' (sint.Z i) ga.pend _ w Hi.1 $$ [Hap] as -
        · isplit
          · iexact Hap
          · ipureintro; exact Hw_lookup
        simp only [Hb2', _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index b.pend' (sint.Z i) gb.pend _ w2 Hi.1 $$ [Hbp] as -
        · isplit
          · iexact Hbp
          · ipureintro; exact Hw2_lookup
        wp_apply wp_inputEqual w w2
        wp_if_destruct
        · wp_for_post
          iframe
          iexists i + W64 1, _
          iframe
          ipureintro
          refine ⟨by word, by word, ?_⟩
          rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one,
            List.take_add_one, Hi.2.2, Hw_lookup, Hw2_lookup, Hif]
        · have hne : ga ≠ gb := fun h => Hif (by
            subst h; rw [Hw_lookup] at Hw2_lookup; cases Hw2_lookup; rfl)
          wp_for_post
          rw [decide_eq_false hne]
          iapply HΦ; itrivial
      · have h1 : ga.pend.length = sint.nat i := by word
        have h2 : gb.pend.length = sint.nat i := by rw [Hlb.1, ← Heq]; word
        have heq : ga.pend = gb.pend := by
          have := Hi.2.2
          rwa [← h1, List.take_length, h1, ← h2, List.take_length] at this
        have hg : ga = gb := by
          cases ga; cases gb
          simp only [linkv.PCfg.mk.injEq] at heq Hst ⊢
          exact ⟨Hst, heq⟩
        rw [decide_eq_true hg]
        iapply HΦ; itrivial
    · rw [decide_eq_false (fun h => Hif (by subst h; word))]
      iapply HΦ; itrivial
  · rw [decide_eq_false (fun h => Hif (by rw [h]))]
    iapply HΦ; itrivial

end proof

end k8setcd3
end EtcdGrove
end Perennial
