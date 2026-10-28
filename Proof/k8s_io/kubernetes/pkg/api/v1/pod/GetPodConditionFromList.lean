/-
Proof of `Spec/k8s_io/kubernetes/pkg/api/v1/pod/GetPodConditionFromList.lean`. Lean-first.
-/
module

public import Spec.k8s_io.kubernetes.pkg.api.v1.pod.GetPodConditionFromList

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsctl

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.kubernetes.pkg.api.v1.pod.Assumptions]

theorem GetPodConditionFromList.wp_proof : GetPodConditionFromList.spec (GF := GF) (hG := hG) := by
  intro s dq cs t
  wp_start as Hs
  iunfold ownSliceD at Hs
  icases Hs with ⟨%vs, Hsl, Hl⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Hl
  ihave %Hf := conds_fields dq vs cs $$ Hl
  wp_auto
  wp_if_destruct
  · -- a nil slice: no condition
    have hs0 : vs = [] := by
      have : sint.nat slice.nil.len = 0 := rfl
      apply List.eq_nil_of_length_eq_zero; omega
    have hc0 : cs = [] := by subst hs0; exact List.eq_nil_of_length_eq_zero Hlen2.symm
    iapply HΦ
    isplitl
    · iunfold ownSliceD; iexists vs; iframe
    · ipureintro; simp [condResult, hc0, condFind]
  rename_i ip2
  ihave HI : (∃ (j x : w64), "i" ∷ i_ptr ↦ j ∗ "i2" ∷ ip2 ↦ x ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len ∧
        ∀ (k : Nat) (c : kd.core.PodCondition), k < sint.nat j → cs[k]? = some c → c.Type' ≠ t⌝ ∗
      "Hsl" ∷ s ↦*{dq} vs ∗ "Hl" ∷ ([∗list] x;e ∈ vs;cs, kd.core.PodCondition.own x dq e) ∗
      "conditionType" ∷ conditionType_ptr ↦ t ∗ "conditions" ∷ conditions_ptr ↦ s : IProp GF)
    $$ [-HΦ]
  · iexists W64 0, _
    iframe
    ipureintro
    refine ⟨by word, by word, fun k c hk _ => by exfalso; simp at hk; omega⟩
  wp_for HI
  by_cases hlt : sint.Z j < sint.Z s.len
  · simp only [hlt, _root_.decide_true, ↓reduceIte]
    wp_auto
    obtain ⟨v, hv⟩ : ∃ v, vs[sint.nat j]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    obtain ⟨c, hc⟩ : ∃ c, cs[sint.nat j]? = some c :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    have hvc := forall2_lookup Hf _ v c hv hc
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := ⟨Hj.1, hlt⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index s (sint.Z j) vs _ v Hj.1) $$ [Hsl] as Hsl
    · iframe; ipureintro; simpa [sint.nat] using hv
    simp only [hb, _root_.and_self, ↓reduceIte]
    icases ownSlice_elem_acc (sint.Z j) v s dq vs Hj.1 (by simpa [sint.nat] using hv) $$ Hsl
      with ⟨Hv, Hsl⟩
    wp_auto
    icases typedPointsto_not_null_dup _ _ _ $$ Hv with ⟨Hv, %Hvnn⟩
    iStructNamedSuffix Hv "_c"
    wp_auto
    ihave Hv := typedPointsto_combine _ v _ Hvnn $$
      [Type'_c ObservedGeneration_c Status_c LastProbeTime_c LastTransitionTime_c Reason_c Message_c]
    · simp only [TypedPointsto.typedPointstoDef]
      iframe
    ihave Hsl := Hsl $$ %v Hv
    rw [show (sint.Z j).toNat = sint.nat j from rfl, list_set_lookup_self vs _ v hv]
    obtain ⟨hty, -, -⟩ := hvc
    wp_if_destruct
    · -- found
      simp only [hb, _root_.and_self, ↓reduceIte]
      wp_auto
      wp_for_post
      iapply HΦ
      isplitl
      · iunfold ownSliceD; iexists vs; iframe
      · ipureintro
        have hfind := condFind_found _ cs (sint.nat j) c
          (fun k c' hk hc' => Hj.2.2 k c' (by omega) hc') hc hty.symm
        simp only [condResult, hfind]
        refine ⟨by word, ?_⟩
        rw [show ((sint.nat j : Nat) : Int) = sint.Z j by word]
    · wp_for_post
      iframe
      iexists j + W64 1, j
      iframe
      ipureintro
      refine ⟨by word, by word, ?_⟩
      intro k c' hk hc'
      by_cases hkj : k < sint.nat j
      · exact Hj.2.2 k c' hkj hc'
      · have hk' : k = sint.nat j := by word
        subst hk'
        rw [hc] at hc'; cases hc'
        rw [← hty]; exact Hif
  · simp only [hlt, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    isplitl
    · iunfold ownSliceD; iexists vs; iframe
    · ipureintro
      have hnone : condFind cs t = none := condFind_none t cs (fun k c' hc' =>
        Hj.2.2 k c' (by have := (List.getElem?_eq_some_iff.1 hc').1; word) hc')
      simp only [condResult, hnone]
      simp

end proof

end dsctl
end EtcdGrove
end Perennial
