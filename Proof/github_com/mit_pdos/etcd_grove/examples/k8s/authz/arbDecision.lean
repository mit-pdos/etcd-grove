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
  intro hdepth
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
    iunfold isWFDecisionLe
    iexists .deny
    iframe #
    ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
  · wp_auto
    wp_apply wp_arbReason as %r _
    (try wp_auto)
    wp_apply wp_arbErr as %e #He
    (try wp_auto)
    wp_apply (wp_ConditionsAwareDecisionAllow r e) $$ [] as %d #Hd
    · iexact He
    (try wp_auto)
    iapply HΦ
    iunfold isWFDecisionLe
    iexists .allow
    iframe #
    ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
  · wp_auto
    wp_apply wp_arbReason as %r _
    (try wp_auto)
    wp_apply wp_arbErr as %e #He
    (try wp_auto)
    wp_apply (wp_ConditionsAwareDecisionNoOpinion r e) $$ [] as %d #Hd
    · iexact He
    (try wp_auto)
    iapply HΦ
    iunfold isWFDecisionLe
    iexists .noOpinion
    iframe #
    ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
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
    iapply isWFDecisionLe_weaken
    isplitl []
    · iexact Hd
    ipureintro; omega
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
      iapply isWFDecisionLe_weaken
      isplitl []
      · iexact Hd
      ipureintro; omega
    · rw [decide_eq_false hd0]
      wp_auto
      ihave Hu := ownBuilder_zero u_ptr $$ u
      wp_apply wp_Int63n as %n %Hn
      · ipureintro; decide
      (try wp_auto)
      have hdm : uint.nat (depth - W64 1) + 1 = uint.nat depth := by word
      ihave HI : (∃ (j : w64) (ks : List Dec),
          "i" ∷ i_ptr ↦ j ∗ "Hu" ∷ ownBuilder u_ptr ks ∗
          "%Hks" ∷ ⌜Dec.depthL ks < uint.nat depth⌝ : IProp GF) $$ [i Hu]
      · iexists W64 0, []
        iframe
        ipureintro; simp only [Dec.depthL]; omega
      wp_for HI
      by_cases Hlt : sint.Z j < sint.Z n
      · rw [decide_eq_true Hlt]; simp only [↓reduceIte]
        (try wp_auto)
        wp_apply wp_arbName as %nm _
        (try wp_auto)
        wp_apply (IH (uint.nat (depth - W64 1)) (by subst hk; word) (depth - W64 1) rfl (by omega))
          as %d' #Hwf'
        iunfold isWFDecisionLe at Hwf'
        icases Hwf' with ⟨%m', #Hd', %Hm'⟩
        have hks' := Dec.depthL_add_le (Dec.cuadL ks) ks m' (uint.nat (depth - W64 1)) (by omega) Hm'.2
        (try wp_auto)
        wp_apply (wp_ConditionsAwareDecisionUnion_Add u_ptr ks nm d' m') $$ [$Hu] as Hu
        · iframe #
          ipureintro; exact ⟨Hm'.1, by omega⟩
        (try wp_auto)
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro; omega
      · rw [decide_eq_false Hlt]
        simp only [Bool.false_eq_true, ↓reduceIte]
        (try wp_auto)
        wp_apply (wp_ConditionsAwareDecisionUnion_ToDecision u_ptr ks) $$ [$Hu] as %d ⟨#Hd, -⟩
        (try wp_auto)
        iapply HΦ
        iapply isWFDecisionLe_weaken
        isplitl []
        · iexact Hd
        ipureintro; omega

end proof

end k8s_authz
end EtcdGrove
end Perennial
