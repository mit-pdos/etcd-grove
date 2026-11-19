/-
`schema.List.Equals`: a member of the recursion cluster `schema.EqualsRec` (`EqualsRec.lean`); its proof is the
projection of the cluster's (its body is `List__EqualsBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.List__EqualsBody
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

theorem schema.List.Equals.wp_proofBody :
    schema.List.Equals.specBody (GF := GF) := by
  unfold schema.List.Equals.specBody schema.EqualsRec.specI schema.Atom.Equals.specI
    schema.List.Equals.specI schema.Map.Equals.specI schema.StructField.Equals.specI
    schema.TypeRef.Equals.specI
  iintro #IH
  iintro %a %b %e %e' %rel %rel' %ks %ks'
  wp_start as ⟨#Ha, #Hb⟩
  icases isListRep_elim_law_holds a e rel ks $$ Ha with ⟨%va, %ksla, #Hva, %hva, #Hksa, #Hea⟩
  icases isListRep_elim_law_holds b e' rel' ks' $$ Hb with ⟨%vb, %kslb, #Hvb, %hvb, #Hksb, #Heb⟩
  cases va with | mk eta era ksa0 =>
  cases vb with | mk etb erb ksb0 =>
  simp only at hva hvb
  obtain ⟨rfl, rfl⟩ := hva
  obtain ⟨rfl, rfl⟩ := hvb
  ihave %Hlena := ownSlice_len $$ Hksa
  ihave %Hlenb := ownSlice_len $$ Hksb
  ihave %Hane := typedPointsto_not_null $$ Hva
  ihave %Hbne := typedPointsto_not_null $$ Hvb
  wp_auto
  wp_if_destruct
  all_goals try (exact (Hane rfl).elim)
  all_goals try wp_if_destruct
  all_goals try (exact (Hbne rfl).elim)
  ihave Hva2 := Hva
  iStructNamedSuffix Hva2 "a"
  ihave Hvb2 := Hvb
  iStructNamedSuffix Hvb2 "b"
  ihave ⟨-, -, -, -, #HT⟩ := IH
  ihave #Hoa := (isTypeRefOpt_some_law_holds eta e).2 $$ Hea
  ihave #Hob := (isTypeRefOpt_some_law_holds etb e').2 $$ Heb
  wp_apply HT $$ %(a.[schema.List', go!"ElementType"]) %(b.[schema.List', go!"ElementType"])
    %DFrac.discard %DFrac.discard %eta %etb %(some e) %(some e')
    as %r1 ⟨-, -, %hr1⟩
  · iframe; iframe #
  cases r1
  · -- the element types differ
    wp_auto
    iapply HΦ
    ipureintro
    simp only [Bool.false_eq_true, false_iff, Option.some.injEq] at hr1 ⊢
    rintro ⟨rfl, -, -⟩; exact hr1 rfl
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
          "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z ksa0.len ∧
            ks.take (sint.nat n) = ks'.take (sint.nat n)⌝) $$ [i Higo]
      · iexists W64 0, _
        iframe
        ipureintro
        refine ⟨by word, by word, by rw [show sint.nat (W64 0) = 0 from rfl]; simp⟩
      wp_for IH2
      wp_if_destruct
      · have Hlt : sint.nat n < ks.length := by
          rw [Hlena.1]; have h1 := Hn.1; have h2 := Hif
          simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
        obtain ⟨x, Hx⟩ : ∃ x, ks[sint.nat n]? = some x := ⟨_, List.getElem?_eq_getElem Hlt⟩
        have Hlt' : sint.nat n < ks'.length := by
          rw [Hlenb.1, ← Hleq]; have h1 := Hn.1; have h2 := Hif
          simp only [sint.nat, sint.Z] at h1 h2 ⊢; omega
        obtain ⟨y, Hy⟩ : ∃ y, ks'[sint.nat n]? = some y := ⟨_, List.getElem?_eq_getElem Hlt'⟩
        have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ksa0.len := ⟨Hn.1, Hif⟩
        simp only [Hbnd, and_self, ↓reduceIte]
        wp_apply wp_load_slice_index ksa0 (sint.Z n) ks DFrac.discard x Hn.1 $$ [] as _
        · iframe #; ipureintro; exact Hx
        simp only [Hbnd, and_self, ↓reduceIte]
        wp_apply wp_load_slice_index ksa0 (sint.Z n) ks DFrac.discard x Hn.1 $$ [] as _
        · iframe #; ipureintro; exact Hx
        have Hbnd' : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ksb0.len := ⟨Hn.1, by rw [← Hleq]; exact Hif⟩
        simp only [Hbnd', and_self, ↓reduceIte]
        wp_apply wp_load_slice_index ksb0 (sint.Z n) ks' DFrac.discard y Hn.1 $$ [] as _
        · iframe #; ipureintro; exact Hy
        wp_if_destruct
        · -- equal keys: on to the next
          wp_for_post
          iframe
          iexists n + W64 1, n
          iframe
          ipureintro
          refine ⟨by word, by word, ?_⟩
          rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one, List.take_add_one,
            Hx, Hy, Hn.2.2, Hif]
        · -- different keys: false
          wp_for_post
          iapply HΦ
          ipureintro
          simp only [Bool.false_eq_true, false_iff, Prod.mk.injEq, _root_.true_and]
          rintro rfl
          rw [Hx] at Hy; cases Hy; exact Hif rfl
      · iapply HΦ
        ipureintro
        have hn1 : sint.nat n = ks.length := by word
        have hn2 : sint.nat n = ks'.length := by word
        have hks := Hn.2.2
        have hl : ks.length = ks'.length := by rw [← hn1, ← hn2]
        rw [hn1, List.take_length, hl, List.take_length] at hks
        simp [hks]
    · iapply HΦ
      ipureintro
      simp only [Bool.false_eq_true, false_iff, Prod.mk.injEq, _root_.true_and]
      intro h
      apply Hif
      have h1 := Hlena.1
      have h2 := Hlenb.1
      rw [h] at h1
      word
  · iapply HΦ
    ipureintro
    simp only [Bool.false_eq_true, false_iff, Prod.mk.injEq, not_and]
    intro _ h; subst h; exact absurd rfl Hif

end proof

end smd
end EtcdGrove
end Perennial
