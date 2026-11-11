module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histEqual
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.histLen
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.storeEqual

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

theorem histEqual.wp_proof
    (wp_histLen : histLen.spec (GF := GF) (hG := hG))
    (wp_storeEqual : storeEqual.spec (GF := GF) (hG := hG)) :
    histEqual.spec (GF := GF) (hG := hG) := by
  intro a b ha hb
  wp_start as ⟨#Ha, #Hb, %Hl⟩
  wp_auto
  wp_apply wp_histLen $$ [$Ha]
  wp_apply wp_histLen $$ [$Hb]
  wp_if_destruct
  · have hlen : ha.length = hb.length := by
      have := Hl; have := Hif; word
    ihave HI : (∃ (ca cb : Loc) (la lb t : List GSt),
        "a" ∷ a_ptr ↦ ca ∗ "b" ∷ b_ptr ↦ cb ∗ "#Hca" ∷ histOwn ca la ∗ "#Hcb" ∷ histOwn cb lb ∗
        "%Hc" ∷ ⌜ha = la ++ t ∧ hb = lb ++ t ∧ la.length = lb.length⌝ : IProp GF) $$ [a b]
    · iexists a, b, ha, hb, []
      isplitl [a]
      · iexact a
      isplitl [b]
      · iexact b
      isplit
      · iexact Ha
      isplit
      · iexact Hb
      · ipureintro; simp [hlen]
    wp_for HI
    wp_if_destruct
    · have hne0 : ca ≠ cb := by
        have := GoGlobalContext.intoVal_inj_bool Hif; simpa using this
      rcases List.eq_nil_or_concat la with rfl | ⟨la', s0, hea⟩
      · have : lb = [] := List.eq_nil_of_length_eq_zero (by rw [← Hc.2.2]; rfl)
        subst this
        icases (histOwn_nil ca).1 $$ Hca with %H1
        icases (histOwn_nil cb).1 $$ Hcb with %H2
        exact absurd (H1.trans H2.symm) hne0
      rcases List.eq_nil_or_concat lb with rfl | ⟨lb', s1, heb⟩
      · rw [hea] at Hc; simp at Hc
      rw [List.concat_eq_append] at hea heb; subst hea heb
      icases (histOwn_snoc ca la' s0).1 $$ Hca with ⟨%na, #Hpa, #Hsa, %Hna, #Hra⟩
      icases (histOwn_snoc cb lb' s1).1 $$ Hcb with ⟨%nb, #Hpb, #Hsb, %Hnb, #Hrb⟩
      iStructNamedPrefix Hpa "a_"
      iStructNamedPrefix Hpb "b_"
      wp_auto
      wp_apply wp_storeEqual na.st' nb.st' s0 s1 $$ [$Hsa $Hsb]
      have hl' : la'.length = lb'.length := by
        have := Hc.2.2; simp only [List.length_append, List.length_singleton] at this; omega
      wp_if_destruct
      · (try wp_auto)
        wp_for_post
        iframe
        iexists na.prev', nb.prev', la', lb', s0 :: t
        iframe
        isplit
        · iexact Hra
        isplit
        · iexact Hrb
        · ipureintro
          refine ⟨by rw [Hc.1]; simp, by rw [Hc.2.1, ← Hif]; simp, hl'⟩
      · have hne : ha ≠ hb := by
          intro he
          rw [Hc.1, Hc.2.1] at he
          simp only [List.append_assoc, List.singleton_append] at he
          have := (List.append_inj he hl').2
          exact Hif (List.cons.inj this).1
        wp_for_post
        (try wp_auto)
        rw [decide_eq_false hne]
        iapply HΦ; itrivial
    · have hca : ca = cb :=
        Classical.byContradiction fun h => Hif (by simp [h])
      subst hca
      icases histOwn_agree _ _ _ $$ Hca Hcb with %Hag
      have he : ha = hb := by rw [Hc.1, Hc.2.1, Hag Hc.2.2]
      simp only [decide_true, Bool.not_true, ↓reduceIte]
      (try wp_auto)
      rw [decide_eq_true he]
      iapply HΦ; itrivial
  · have hne : ha ≠ hb := by
      intro he; subst he; exact Hif rfl
    rw [decide_eq_false hne]
    iapply HΦ; itrivial

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
