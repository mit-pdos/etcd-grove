/-
The proof of `ConditionsMap.PossibleDecisions.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/authorizer/ConditionsMap__PossibleDecisions.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsMap__PossibleDecisions
public import Spec.k8s_io.apimachinery.pkg.util.sets.New
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Insert
public import Proof.k8s_io.apimachinery.pkg.util.sets.PtrMethods
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.B1Lemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer sets

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

theorem ConditionsMap.PossibleDecisions.wp_proof
    (wp_sets_New : EtcdGrove.sets.New.spec (GF := GF) (hG := hG))
    (wp_Set__Insert : EtcdGrove.sets.Set.Insert.spec (GF := GF) (hG := hG)) :
    ConditionsMap.PossibleDecisions.spec (GF := GF) (hG := hG) := by
  intro c dq dq' dn al
  wp_start as ⟨Hdn, Hal⟩
  simp only [DecisionNoOpinion, DecisionAllow, DecisionDeny]
  wp_auto
  wp_apply wp_slice_literal (V := w64) [W64 2]
  isplitr
  · ipureintro; rfl
  iintro %nsl ⟨Hnsl, -⟩
  try wp_auto
  wp_apply (wp_sets_New (K := w64) (T := Decision.ty) _ _ [W64 2]) $$ [Hnsl] as %m ⟨Hm, -⟩
  · iexact Hnsl
  try wp_auto
  ihave %Hall := ownSlice_len _ _ _ $$ Hal
  ihave %Hdnl := ownSlice_len _ _ _ $$ Hdn
  rw [len_pos_iff al _ Hall.1 Hall.2]
  ihave HS : (∃ S, m ↦$ S ∗ ⌜setIs S ⟨false, false, true⟩⌝ : IProp GF) $$ [Hm]
  · iexists _; iframe Hm; ipureintro; exact setIs_new [W64 2] (by simp)
  icases HS with ⟨%S, Hm, %HS⟩
  cases hA : al.isEmpty
  all_goals first
  | guard_hyp hA : al.isEmpty = false
    simp only [Bool.not_false]
    wp_auto
    wp_apply wp_slice_literal (V := w64) [W64 1]
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    try wp_auto
    wp_apply (Set.wp_ptr_Insert_of wp_Set__Insert possibleDecisions_ptr (DFrac.own 1) m _ _ _ [W64 1])
      $$ [$possibleDecisions $Hm $Hasl] as ⟨possibleDecisions, Hm, -⟩
    ihave HS2 : (∃ S', m ↦$ S' ∗ ⌜setIs S' ⟨false, !al.isEmpty, true⟩⌝ : IProp GF) $$ [Hm]
    · iexists _; iframe Hm; ipureintro
      rw [hA]; exact setIs_congr (setIs_insertAll S _ [W64 1] HS (by simp)) (by decide)
  | simp only [Bool.not_true]
    wp_auto
    ihave HS2 : (∃ S', m ↦$ S' ∗ ⌜setIs S' ⟨false, !al.isEmpty, true⟩⌝ : IProp GF) $$ [Hm]
    · iexists S; iframe Hm; ipureintro; rw [hA]; exact HS
  all_goals
    clear HS S
    icases HS2 with ⟨%S, Hm, %HS⟩
    rw [len_pos_iff dn _ Hdnl.1 Hdnl.2]
    cases hD : dn.isEmpty
    · simp only [Bool.not_false]
      wp_auto
      wp_apply wp_slice_literal (V := w64) [W64 0]
      isplitr
      · ipureintro; rfl
      iintro %dsl ⟨Hdsl, -⟩
      try wp_auto
      wp_apply (Set.wp_ptr_Insert_of wp_Set__Insert possibleDecisions_ptr (DFrac.own 1) m _ _ _ [W64 0])
        $$ [$possibleDecisions $Hm $Hdsl] as ⟨possibleDecisions, Hm, -⟩
      iapply HΦ
      iframe
      ipureintro
      simp only [Dec.pd, hD]
      exact setIs_congr (setIs_insertAll S _ [W64 0] HS (by simp)) (by cases al.isEmpty <;> decide)
    · simp only [Bool.not_true]
      wp_auto
      iapply HΦ
      iframe
      ipureintro
      simp only [Dec.pd, hD]
      exact HS

end proof

end authorizer
end EtcdGrove
end Perennial
