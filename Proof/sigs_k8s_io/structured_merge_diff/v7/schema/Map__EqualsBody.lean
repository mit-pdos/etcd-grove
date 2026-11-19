/-
`schema.Map.Equals`: a member of the recursion cluster `schema.EqualsRec` (`EqualsRec.lean`); its proof is the
projection of the cluster's (its body is `Map__EqualsBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Map__EqualsBody
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : schema.Assumptions]

theorem schema.Map.Equals.wp_proofBody :
    schema.Map.Equals.specBody (GF := GF) := by
  unfold schema.Map.Equals.specBody schema.EqualsRec.specI schema.Atom.Equals.specI
    schema.List.Equals.specI schema.Map.Equals.specI schema.StructField.Equals.specI
    schema.TypeRef.Equals.specI
  iintro #IH
  iintro %a %b %fs %fs' %e %e' %rel %rel'
  wp_start as ⟨#Ha, #Hb⟩
  ihave %Hane := isMapRep_nonnull_law_holds _ _ _ _ $$ Ha
  ihave %Hbne := isMapRep_nonnull_law_holds _ _ _ _ $$ Hb
  icases isMapRep_elim_law_holds _ _ _ _ $$ Ha with
    ⟨%fsla, %sfsa, %etva, #HFa, #Hsfa, %hlena, #Hfa, #HUa, #HEa, #Heta, #HRa⟩
  icases isMapRep_elim_law_holds _ _ _ _ $$ Hb with
    ⟨%fslb, %sfsb, %etvb, #HFb, #Hsfb, %hlenb, #Hfb, #HUb, #HEb, #Hetb, #HRb⟩
  wp_auto
  wp_if_destruct
  all_goals try (exact (Hane rfl).elim)
  all_goals try wp_if_destruct
  all_goals try (exact (Hbne rfl).elim)
  ihave %Hla := ownSlice_len $$ Hsfa
  ihave %Hlb := ownSlice_len $$ Hsfb
  ihave ⟨-, -, -, -, #HT⟩ := IH
  wp_apply HT $$ %(a.[schema.Map, go!"ElementType"]) %(b.[schema.Map, go!"ElementType"])
    %DFrac.discard %DFrac.discard %etva %etvb %e %e'
    as %r1 ⟨-, -, %hr1⟩
  · iframe #
  cases r1
  · wp_auto
    iapply HΦ
    ipureintro
    simp only [Bool.false_eq_true, false_iff] at hr1 ⊢
    rintro h; simp only [Prod.mk.injEq] at h; exact hr1 h.2.1
  have he : e = e' := by simpa using hr1
  subst he
  wp_auto
  wp_if_destruct
  · have hrel : rel = rel' := by
      revert Hif; cases rel <;> cases rel' <;> simp [ElemRel.goName]
    subst hrel
    wp_if_destruct
    · have Hleq := Hif
      rename_i igo
      irename : (igo ↦ zero_val w64 : IProp GF) => Higo
      ihave IH2 : iprop(∃ (n k : w64),
          "i" ∷ i_ptr ↦ n ∗ "Higo" ∷ igo ↦ k ∗
          "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z fsla.len ∧
            fs.take (sint.nat n) = fs'.take (sint.nat n)⌝) $$ [i Higo]
      · iexists W64 0, _
        iframe
        ipureintro
        refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
      wp_for IH2
      wp_if_destruct
      · have Hlt : sint.nat n < sfsa.length := by
          rw [Hla.1]; have h1 := Hn.1; have h2 := Hif
          simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
        have Hlt' : sint.nat n < sfsb.length := by
          rw [Hlb.1, ← Hleq]; have h1 := Hn.1; have h2 := Hif
          simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
        obtain ⟨sf, Hsf⟩ : ∃ x, sfsa[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
        obtain ⟨sf', Hsf'⟩ : ∃ x, sfsb[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt'⟩
        obtain ⟨f, Hf⟩ : ∃ x, fs[sint.nat n]? = some x :=
          ⟨_, List.getElem?_eq_getElem (by rw [← hlena]; exact Hlt)⟩
        obtain ⟨f', Hf'⟩ : ∃ x, fs'[sint.nat n]? = some x :=
          ⟨_, List.getElem?_eq_getElem (by rw [← hlenb]; exact Hlt')⟩
        have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z fsla.len := ⟨Hn.1, Hif⟩
        have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z fslb.len := ⟨Hn.1, by rw [← Hleq]; exact Hif⟩
        simp only [Hbnd, and_self, ↓reduceIte]
        wp_apply wp_load_slice_index fsla (sint.Z n) sfsa DFrac.discard sf Hn.1 $$ [] as _
        · iframe #; ipureintro; exact Hsf
        simp only [Hbnd, Hbnd', and_self, ↓reduceIte]
        ihave Hsfa2 := Hsfa
        ihave Hsfb2 := Hsfb
        icases ownSlice_elem_acc (sint.Z n) sf fsla DFrac.discard sfsa Hn.1 Hsf $$ Hsfa2 with ⟨Hea, -⟩
        icases ownSlice_elem_acc (sint.Z n) sf' fslb DFrac.discard sfsb Hn.1 Hsf' $$ Hsfb2 with ⟨Heb, -⟩
        ihave #Hfsa := Hfa $$ %(sint.nat n) %sf %f %(And.intro Hsf Hf)
        ihave #Hfsb := Hfb $$ %(sint.nat n) %sf' %f' %(And.intro Hsf' Hf')
        ihave ⟨-, -, -, #HS, -⟩ := IH
        wp_auto
        try simp only [Hbnd, Hbnd', and_self, ↓reduceIte]
        wp_apply HS $$ %(sliceIndexRef schema.StructField (sint.Z n) fsla)
          %(sliceIndexRef schema.StructField (sint.Z n) fslb) %DFrac.discard %DFrac.discard
          %sf %sf' %f %f' as %r ⟨-, -, %hr⟩
        · iframe; iframe #
        cases r
        · wp_auto
          wp_for_post
          iapply HΦ
          ipureintro
          simp only [Bool.false_eq_true, false_iff, Prod.mk.injEq, _root_.and_true]
          rintro rfl
          rw [Hf] at Hf'; cases Hf'; simp at hr
        · have hff : f = f' := by simpa using hr
          subst hff
          wp_auto
          wp_for_post
          iframe
          iexists n + W64 1, n
          iframe
          ipureintro
          refine ⟨by word, by word, ?_⟩
          rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one,
            List.take_add_one, Hf, Hf', Hn.2.2]
      · have hn1 : sint.nat n = fs.length := by
          rw [← hlena, Hla.1]; have h1 := Hn.1; have h2 := Hn.2.1
          simp only [sint.nat, sint.Z] at h1 h2 Hif ⊢; omega
        have hn2 : sint.nat n = fs'.length := by
          rw [← hlenb, Hlb.1, ← Hleq]; have h1 := Hn.1; have h2 := Hn.2.1
          simp only [sint.nat, sint.Z] at h1 h2 Hif ⊢; omega
        have hfs : fs = fs' := by
          have hks := Hn.2.2
          have hl : fs.length = fs'.length := by rw [← hn1, ← hn2]
          rw [hn1, List.take_length, hl, List.take_length] at hks
          exact hks
        subst hfs
        ihave IH3 : iprop(∃ k : w64, "i" ∷ i_ptr ↦ k ∗ "%Hk" ∷ ⌜k = W64 0⌝) $$ [i]
        · iexists W64 0; iframe; ipureintro; rfl
        wp_for IH3
        wp_if_destruct
        · exfalso; subst Hk; revert Hif; decide
        · iapply HΦ
          ipureintro
          simp
    · iapply HΦ
      ipureintro
      simp only [Bool.false_eq_true, false_iff, Prod.mk.injEq, _root_.and_true]
      intro h
      apply Hif
      have h1 := Hla.1
      have h2 := Hlb.1
      rw [hlena, h, ← hlenb] at h1
      word
  · iapply HΦ
    ipureintro
    simp only [Bool.false_eq_true, false_iff, Prod.mk.injEq, _root_.true_and]
    intro h; rw [h.2] at Hif; exact Hif rfl

end proof

end smd
end EtcdGrove
end Perennial
