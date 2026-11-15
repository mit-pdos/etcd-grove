module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histAt

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore mcfg hnode state labelSel fieldSel)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

theorem histAt.wp_proof :
    histAt.spec (GF := GF) (hG := hG) := by
  intro h hs r
  wp_start as ⟨#Hh, %Hl⟩
  wp_auto
  ihave HI : (∃ (cur : Loc) (l : List GSt), "h" ∷ h_ptr ↦ cur ∗ "#Hc" ∷ histOwn cur l ∗
      "%Hc" ∷ ⌜histAtL hs r = histAtL l r ∧ l.length ≤ hs.length⌝ : IProp GF) $$ [h]
  · iexists h, hs
    isplitl [h]
    · iexact h
    isplit
    · iexact Hh
    · ipureintro; exact ⟨rfl, Nat.le_refl _⟩
  wp_for HI
  rcases List.eq_nil_or_concat l with rfl | ⟨l', s0, he⟩
  · icases (histOwn_nil cur).1 $$ Hc with %Hn
    subst Hn
    wp_if_destruct
    · (try wp_auto)
      rw [Hc.1, histAtL_nil]
      iapply HΦ
      unfold storeOwn
      isplit
      · simp only [zero_val, zSt]
        iapply ownSlice_nil
      · ipureintro; rfl
    · exact absurd rfl Hif
  · rw [List.concat_eq_append] at he; subst he
    icases (histOwn_snoc cur l' s0).1 $$ Hc with ⟨%hn, #Hp, #Hs, %Hn, #Hr⟩
    icases (typedPointsto_not_null _ _ _) $$ Hp with %Hnn
    wp_if_destruct
    · exact absurd rfl Hnn
    iStructNamed Hp
    wp_auto
    have hlt : l'.length + 1 < 2 ^ 64 := by
      have := Hc.2; simp only [List.length_append, List.length_singleton] at this; omega
    have hnl : uint.nat hn.n' = l'.length + 1 := by rw [Hn]; word
    wp_if_destruct
    · have hgt : uint.Z r < uint.Z hn.n' :=
        of_decide_eq_true (GoGlobalContext.intoVal_inj_bool Hif)
      (try wp_auto)
      wp_for_post
      iframe
      iexists hn.prev', l'
      isplitl [h]
      · iexact h
      isplit
      · iexact Hr
      · ipureintro
        refine ⟨?_, ?_⟩
        · rw [Hc.1]; apply histAtL_snoc_le
          have h1 : uint.nat r < uint.nat hn.n' := by word
          omega
        · have := Hc.2; simp only [List.length_append] at this; omega
    · have hle : ¬ uint.Z r < uint.Z hn.n' := fun h => Hif (by rw [decide_eq_true h])
      rw [decide_eq_false hle]
      simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      rw [decide_eq_false Hnn]
      wp_auto
      have h1 : l'.length < uint.nat r := by
        have : uint.nat hn.n' ≤ uint.nat r := by word
        omega
      rw [Hc.1, histAtL_snoc_gt _ _ _ h1]
      iapply HΦ
      iexact Hs

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
