/-
The proof of `ConditionsAwareDecisionFromParts.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/authorizer/ConditionsAwareDecisionFromParts.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionFromParts
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionAllow
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionNoOpinion
public import Spec.k8s_io.apimachinery.pkg.util.errors.NewAggregate
public import Spec.fmt.ErrorfAny

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

theorem ConditionsAwareDecisionFromParts.wp_proof
    (wp_ConditionsAwareDecisionDeny : EtcdGrove.authorizer.ConditionsAwareDecisionDeny.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionAllow : EtcdGrove.authorizer.ConditionsAwareDecisionAllow.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionNoOpinion : EtcdGrove.authorizer.ConditionsAwareDecisionNoOpinion.spec (GF := GF) (hG := hG))
    (wp_NewAggregate : EtcdGrove.utilerrors.NewAggregate.spec (GF := GF) (hG := hG))
    (wp_ErrorfAny : EtcdGrove.fmt.ErrorfAny.spec (GF := GF) (hG := hG)) :
    ConditionsAwareDecisionFromParts.spec (GF := GF) (hG := hG) := by
  intro k r e
  wp_start
  wp_auto
  unfold Dec.ofWord
  by_cases h1 : k = W64 1
  · rw [decide_eq_true h1]; simp only [h1, ↓reduceIte]
    wp_auto
    wp_apply (wp_ConditionsAwareDecisionAllow r e) as %d #Hd
    iapply HΦ
    iexact Hd
  · rw [decide_eq_false h1]; simp only [h1, ↓reduceIte]
    wp_auto
    by_cases h2 : k = W64 2
    · rw [decide_eq_true h2]; simp only [h2, ↓reduceIte]
      wp_auto
      wp_apply (wp_ConditionsAwareDecisionNoOpinion r e) as %d #Hd
      iapply HΦ
      iexact Hd
    · rw [decide_eq_false h2]; simp only [h2, ↓reduceIte]
      wp_auto
      by_cases h0 : k = W64 0
      · rw [decide_eq_true h0]
        wp_auto
        wp_apply (wp_ConditionsAwareDecisionDeny r e) as %d #Hd
        iapply HΦ
        iexact Hd
      · rw [decide_eq_false h0]
        wp_auto
        wp_apply wp_slice_literal (V := GoAny) [_]
        isplitr
        · ipureintro; rfl
        iintro %asl ⟨Hasl, -⟩
        try wp_auto
        wp_apply wp_ErrorfAny _ _ _ _ $$ [Hasl] as %ef ⟨-, -⟩
        · iexact Hasl
        try wp_auto
        wp_apply wp_slice_literal (V := GoInterface) [_, _]
        isplitr
        · ipureintro; rfl
        iintro %esl ⟨Hesl, -⟩
        try wp_auto
        wp_apply wp_NewAggregate _ (DFrac.own 1) [e, ef] $$ [Hesl] as %a -
        · iexact Hesl
        try wp_auto
        wp_apply (wp_ConditionsAwareDecisionDeny r a) as %d #Hd
        iapply HΦ
        iexact Hd

end proof

end authorizer
end EtcdGrove
end Perennial
