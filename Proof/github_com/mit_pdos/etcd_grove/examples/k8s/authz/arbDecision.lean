/-
The proof of `arbDecision.spec`
(`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/authz/arbDecision.lean`). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbDecision
public import Spec.math.rand.Int63n
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbReason
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbErr
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionAllow
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionNoOpinion
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbConds
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionConditionsMap
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.authz.arbName
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__Add
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__ToDecision
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.authz.B6Lemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_authz

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer k8s_io.apiserver.pkg.authorization.union github_com.mit_pdos.etcd_grove.examples.k8s.authz EtcdGrove.authorizer EtcdGrove.union

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.authz.Assumptions]

theorem arbDecision.wp_proof
    (wp_Int63n : EtcdGrove.rand.Int63n.spec (GF := GF) (hG := hG))
    (wp_arbReason : EtcdGrove.k8s_authz.arbReason.spec (GF := GF) (hG := hG))
    (wp_arbErr : EtcdGrove.k8s_authz.arbErr.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionDeny : EtcdGrove.authorizer.ConditionsAwareDecisionDeny.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionAllow : EtcdGrove.authorizer.ConditionsAwareDecisionAllow.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionNoOpinion : EtcdGrove.authorizer.ConditionsAwareDecisionNoOpinion.spec (GF := GF) (hG := hG))
    (wp_arbConds : EtcdGrove.k8s_authz.arbConds.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionConditionsMap : EtcdGrove.authorizer.ConditionsAwareDecisionConditionsMap.spec (GF := GF) (hG := hG))
    (wp_arbName : EtcdGrove.k8s_authz.arbName.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionUnion_Add : EtcdGrove.authorizer.ConditionsAwareDecisionUnion.Add.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionUnion_ToDecision : EtcdGrove.authorizer.ConditionsAwareDecisionUnion.ToDecision.spec (GF := GF) (hG := hG)) :
    arbDecision.spec (GF := GF) (hG := hG) := by
  intro depth
  induction hk : uint.nat depth using Nat.strongRecOn generalizing depth with
  | _ k IH =>
  intro hdepth hsize
  subst hk
  have h4 : 1 ≤ 4 ^ uint.nat depth := Nat.one_le_pow _ _ (by decide)
  wp_start
  wp_auto
  wp_apply wp_Int63n as %x %Hx
  · ipureintro; decide
  rcases int63n_5_cases x Hx with rfl | rfl | rfl | rfl | rfl
  · wp_auto
    wp_apply wp_arbReason as %r _
    (try wp_auto)
    wp_apply wp_arbErr as %e #He
    (try wp_auto)
    wp_apply (wp_ConditionsAwareDecisionDeny r e) $$ [] as %d #Hd
    · iexact He
    (try wp_auto)
    iapply HΦ
    iapply isWFDecisionBnd_leaf'
    isplitl []
    · iexact Hd
    ipureintro; exact ⟨trivial, rfl, h4⟩
  · wp_auto
    wp_apply wp_arbReason as %r _
    (try wp_auto)
    wp_apply wp_arbErr as %e #He
    (try wp_auto)
    wp_apply (wp_ConditionsAwareDecisionAllow r e) $$ [] as %d #Hd
    · iexact He
    (try wp_auto)
    iapply HΦ
    iapply isWFDecisionBnd_leaf'
    isplitl []
    · iexact Hd
    ipureintro; exact ⟨trivial, rfl, h4⟩
  · wp_auto
    wp_apply wp_arbReason as %r _
    (try wp_auto)
    wp_apply wp_arbErr as %e #He
    (try wp_auto)
    wp_apply (wp_ConditionsAwareDecisionNoOpinion r e) $$ [] as %d #Hd
    · iexact He
    (try wp_auto)
    iapply HΦ
    iapply isWFDecisionBnd_leaf'
    isplitl []
    · iexact Hd
    ipureintro; exact ⟨trivial, rfl, h4⟩
  · wp_auto
    wp_apply wp_arbConds as %s1 ⟨%c1, Hs1, #Hc1⟩
    (try wp_auto)
    wp_apply wp_arbConds as %s2 ⟨%c2, Hs2, #Hc2⟩
    (try wp_auto)
    wp_apply wp_arbConds as %s3 ⟨%c3, Hs3, #Hc3⟩
    (try wp_auto)
    wp_apply (wp_ConditionsAwareDecisionConditionsMap s1 s2 s3 _ _ _ c1 c2 c3) $$ [$Hs1 $Hs2 $Hs3]
      as %d ⟨#Hd, -⟩
    · iapply (BigSepL.bigSepL_append (l₁ := c1 ++ c2) (l₂ := c3)).2
      isplitl
      · iapply (BigSepL.bigSepL_append (l₁ := c1) (l₂ := c2)).2
        isplitl
        · iexact Hc1
        iexact Hc2
      iexact Hc3
    (try wp_auto)
    iapply HΦ
    iapply isWFDecisionBnd_weaken
    isplitl []
    · iapply isWFDecisionLe_zero_bnd
      iexact Hd
    ipureintro; exact ⟨Nat.zero_le _, h4⟩
  · wp_auto
    by_cases hd0 : depth = W64 0
    · rw [decide_eq_true hd0]
      wp_auto
      wp_apply wp_arbConds as %s1 ⟨%c1, Hs1, #Hc1⟩
      (try wp_auto)
      wp_apply wp_arbConds as %s2 ⟨%c2, Hs2, #Hc2⟩
      (try wp_auto)
      wp_apply wp_arbConds as %s3 ⟨%c3, Hs3, #Hc3⟩
      (try wp_auto)
      wp_apply (wp_ConditionsAwareDecisionConditionsMap s1 s2 s3 _ _ _ c1 c2 c3) $$ [$Hs1 $Hs2 $Hs3]
        as %d ⟨#Hd, -⟩
      · iapply (BigSepL.bigSepL_append (l₁ := c1 ++ c2) (l₂ := c3)).2
        isplitl
        · iapply (BigSepL.bigSepL_append (l₁ := c1) (l₂ := c2)).2
          isplitl
          · iexact Hc1
          iexact Hc2
        iexact Hc3
      (try wp_auto)
      iapply HΦ
      iapply isWFDecisionBnd_weaken
      isplitl []
      · iapply isWFDecisionLe_zero_bnd
        iexact Hd
      ipureintro; exact ⟨Nat.zero_le _, h4⟩
    · rw [decide_eq_false hd0]
      wp_auto
      ihave Hu := ownBuilder_zero u_ptr authzNameMax $$ u
      wp_apply wp_Int63n as %n %Hn
      · ipureintro; decide
      (try wp_auto)
      have hdm : uint.nat (depth - W64 1) + 1 = uint.nat depth := by word
      have h4d : 4 ^ uint.nat depth = 4 ^ uint.nat (depth - W64 1) * 4 := by
        rw [← hdm, Nat.pow_succ]
      have h4' : 1 ≤ 4 ^ uint.nat (depth - W64 1) := Nat.one_le_pow _ _ (by decide)
      have hfitc : Dec.foldBound authzSizeMax authzDepthMax authzNameMax <
          _root_.Perennial.strings.joinMax :=
        Nat.lt_of_le_of_lt (Dec.foldBound_mono (by unfold authzSizeMax authzChainMax; omega)
          (by omega)) authz_foldBound_lt
      ihave HI : (∃ (j : w64) (ks : List Dec) (c : Nat),
          "i" ∷ i_ptr ↦ j ∗ "Hu" ∷ ownBuilder u_ptr ks authzNameMax ∗
          "%Hks" ∷ ⌜Dec.depthL ks < uint.nat depth ∧ sint.Z j = c ∧ c ≤ 3 ∧
            Dec.sizeL ks ≤ c * 4 ^ uint.nat (depth - W64 1)⌝ : IProp GF) $$ [i Hu]
      · iexists W64 0, [], 0
        iframe
        ipureintro; refine ⟨by simp only [Dec.depthL]; omega, rfl, by omega, by simp [Dec.sizeL]⟩
      wp_for HI
      by_cases Hlt : sint.Z j < sint.Z n
      · rw [decide_eq_true Hlt]; simp only [↓reduceIte]
        (try wp_auto)
        wp_apply wp_arbName as %nm %hnm
        (try wp_auto)
        wp_apply (IH (uint.nat (depth - W64 1)) (by word) (depth - W64 1) rfl (by omega)
          (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hsize))
          as %d' #Hwf'
        iunfold isWFDecisionBnd at Hwf'
        icases Hwf' with ⟨%m', #Hd', %Hm', #Hdn'⟩
        have hks' := Dec.depthL_add_le (Dec.cuadL ks) ks m' (uint.nat (depth - W64 1)) (by omega) Hm'.2.1
        have hcn : c + 1 ≤ 3 := by have := Hks.2.1; word
        have hsz' := Dec.sizeL_add_le (Dec.cuadL ks) ks m' ((c + 1) * 4 ^ uint.nat (depth - W64 1))
          (by rw [Nat.add_mul, Nat.one_mul]; have := Hks.2.2.2; have := Hm'.2.2; omega)
        (try wp_auto)
        wp_apply (wp_ConditionsAwareDecisionUnion_Add u_ptr ks nm d' m' authzNameMax) $$ [$Hu] as Hu
        · iframe #
          ipureintro
          have hd16 : uint.nat depth ≤ 16 := hdepth
          exact ⟨Hm'.1, by have := Hm'.2.1; omega, hnm⟩
        (try wp_auto)
        wp_for_post
        iframe
        iexists _, _, c + 1
        iframe
        ipureintro
        refine ⟨by omega, by have := Hks.2.1; word, hcn, hsz'⟩
      · rw [decide_eq_false Hlt]
        simp only [Bool.false_eq_true, ↓reduceIte]
        (try wp_auto)
        have hsz : Dec.sizeL ks + 1 ≤ 4 ^ uint.nat depth := by
          have := Hks.2.2.2
          have := Nat.mul_le_mul_right (4 ^ uint.nat (depth - W64 1)) Hks.2.2.1
          omega
        wp_apply (wp_ConditionsAwareDecisionUnion_ToDecision u_ptr ks authzNameMax
          (Dec.foldFits_of_le _ _ _ _ (by simp only [Dec.size]; omega)
            (by simp only [Dec.depth]; omega) hfitc)) $$ [$Hu] as %d ⟨#Hd, -⟩
        (try wp_auto)
        iapply HΦ
        iapply isWFDecisionBnd_weaken
        isplitl []
        · iexact Hd
        ipureintro; exact ⟨by omega, hsz⟩

end proof

end k8s_authz
end EtcdGrove
end Perennial
