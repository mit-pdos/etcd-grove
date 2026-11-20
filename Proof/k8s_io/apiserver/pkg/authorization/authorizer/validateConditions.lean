/-
The proof of `validateConditions.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/authorizer/validateConditions.lean`). Lean-first (no
Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.validateConditions
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Has
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Insert
public import Spec.fmt.ErrorfAny
public import Spec.k8s_io.apimachinery.pkg.util.validation.field.NewPath
public import Spec.k8s_io.apimachinery.pkg.util.validation.IsDomainPrefixedKey
public import Spec.k8s_io.apimachinery.pkg.util.validation.field.ErrorList__ToAggregate_ptr
public import Proof.k8s_io.apimachinery.pkg.util.sets.PtrMethods
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.B2Lemmas

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer
open _root_.Perennial.github_com.mit_pdos.perennial.goose.model.strings (wp_string_len)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

theorem validateConditions.wp_proof
    (wp_Set__Has : EtcdGrove.sets.Set.Has.spec (GF := GF) (hG := hG))
    (wp_Set__Insert : EtcdGrove.sets.Set.Insert.spec (GF := GF) (hG := hG))
    (wp_ErrorfAny : EtcdGrove.fmt.ErrorfAny.spec (GF := GF) (hG := hG))
    (wp_NewPath : EtcdGrove.field.NewPath.spec (GF := GF) (hG := hG))
    (wp_IsDomainPrefixedKey : EtcdGrove.validation.IsDomainPrefixedKey.spec (GF := GF) (hG := hG))
    (wp_ErrorList_ToAggregate_ptr : EtcdGrove.field.ErrorList.ToAggregate_ptr.spec (GF := GF) (hG := hG)) :
    validateConditions.spec (GF := GF) (hG := hG) := by
  intro seen S s dq cs
  wp_start as ⟨Hseen, Hs, #Hcs⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  ihave HInv : (∃ (j : w64) (cv : GoInterface) (S' : GMap GoString sets.Elem), "i" ∷ i_ptr ↦ j ∗
      "condition" ∷ condition_ptr ↦ cv ∗ "Hseen" ∷ seen ↦$ S' ∗ "Hs" ∷ s ↦*{dq} cs ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len⌝ : IProp GF) $$ [i condition Hseen Hs]
  · iexists W64 0, _, _
    iframe
    ipureintro; constructor <;> word
  wp_for HInv
  by_cases hlt : sint.Z j < sint.Z s.len
  · simp only [hlt, _root_.decide_true, ↓reduceIte]
    wp_auto
    have hjl : sint.nat j < cs.length := by word
    obtain ⟨v, hv⟩ : ∃ v, cs[sint.nat j]? = some v := ⟨_, List.getElem?_eq_getElem hjl⟩
    have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z s.len := ⟨Hj.1, hlt⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index s (sint.Z j) cs _ v Hj.1) $$ [$Hs] as Hs
    · ipureintro; simpa [sint.nat] using hv
    ihave #Hx := BigSepL.bigSepL_lookup hv $$ Hcs
    icases isCondition_elim_b2 v $$ Hx with ⟨%ci, %Hci, #HgetID, #HgetType, #HgetCond, #HgetDesc, -⟩
    subst Hci
    ihave #HgetID' := strMethodOk_elim_b2 ci _ $$ HgetID
    ihave #HgetType' := strMethodOk_elim_b2 ci _ $$ HgetType
    ihave #HgetCond' := strMethodOk_elim_b2 ci _ $$ HgetCond
    ihave #HgetDesc' := strMethodOk_elim_b2 ci _ $$ HgetDesc
    (try wp_auto)
    wp_apply HgetID' as %idv -
    wp_apply (sets.Set.wp_ptr_Has_of wp_Set__Has seenIDs_ptr (DFrac.own 1) seen (DFrac.own 1) S' idv)
      $$ [$seenIDs $Hseen] as ⟨seenIDs, Hseen⟩
    by_cases hh : (S' !! idv).isSome = true
    · simp only [hh, _root_.decide_true]
      wp_auto
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      iintro %sla ⟨Hargs, -⟩
      (try wp_auto)
      wp_apply wp_ErrorfAny _ _ _ _ $$ [Hargs] as %ef -
      · iexact Hargs
      (try wp_auto)
      wp_for_post
      iapply HΦ
      iframe
    simp only [hh, _root_.decide_false]
    wp_auto
    wp_apply wp_slice_literal
    try (isplitr; (ipureintro; rfl))
    iintro %sli ⟨Hsli, -⟩
    (try wp_auto)
    wp_apply (sets.Set.wp_ptr_Insert_of wp_Set__Insert seenIDs_ptr (DFrac.own 1) seen S' _
      (DFrac.own 1) [idv]) $$ [$seenIDs $Hseen $Hsli] as ⟨seenIDs, Hseen, -⟩
    (try wp_auto)
    wp_apply wp_NewPath _ slice.nil (DFrac.own 1) ([] : List GoString) as %p1 -
    · iapply ownSlice_nil
    (try wp_auto)
    wp_apply wp_IsDomainPrefixedKey as %el1 ⟨%errs1, Hel1, #Hok1⟩
    (try wp_auto)
    by_cases he1 : sint.Z (W64 0) < sint.Z el1.len
    · simp only [he1, _root_.decide_true]
      wp_auto
      wp_apply wp_ErrorList_ToAggregate_ptr errs_ptr (DFrac.own 1) el1 (DFrac.own 1) errs1
        $$ [$errs $Hel1] as %agg -
      · iexact Hok1
      (try wp_auto)
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      iintro %sla ⟨Hargs, -⟩
      (try wp_auto)
      wp_apply wp_ErrorfAny _ _ _ _ $$ [Hargs] as %ef -
      · iexact Hargs
      (try wp_auto)
      wp_for_post
      iapply HΦ
      iframe
    simp only [he1, _root_.decide_false]
    wp_auto
    wp_apply HgetCond' as %cnd -
    wp_apply wp_string_len cnd
      as -
    by_cases hc : sint.Z (W64 10240) < sint.Z (W64 cnd.length)
    · simp only [hc, _root_.decide_true]
      wp_auto
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      iintro %sla ⟨Hargs, -⟩
      (try wp_auto)
      wp_apply wp_ErrorfAny _ _ _ _ $$ [Hargs] as %ef -
      · iexact Hargs
      (try wp_auto)
      wp_for_post
      iapply HΦ
      iframe
    simp only [hc, _root_.decide_false]
    wp_auto
    wp_apply HgetType' as %ty -
    wp_apply wp_string_len ty as -
    by_cases ht : W64 ty.length = W64 0
    · simp only [ht, _root_.decide_true, Bool.not_true]
      wp_auto
      wp_apply HgetDesc' as %dsc -
      wp_apply wp_string_len dsc as -
      by_cases hds : sint.Z (W64 1024) < sint.Z (W64 dsc.length)
      · simp only [hds, _root_.decide_true]
        wp_auto
        wp_apply wp_slice_literal
        try (isplitr; (ipureintro; rfl))
        iintro %sla ⟨Hargs, -⟩
        (try wp_auto)
        wp_apply wp_ErrorfAny _ _ _ _ $$ [Hargs] as %ef -
        · iexact Hargs
        (try wp_auto)
        wp_for_post
        iapply HΦ
        iframe
      simp only [hds, _root_.decide_false]
      wp_auto
      wp_for_post
      iframe
      iexists j + W64 1, _, _
      iframe
      ipureintro; constructor <;> word
    simp only [ht, _root_.decide_false, Bool.not_false]
    wp_auto
    wp_apply wp_NewPath _ slice.nil (DFrac.own 1) ([] : List GoString) as %p2 -
    · iapply ownSlice_nil
    (try wp_auto)
    wp_apply wp_IsDomainPrefixedKey as %el2 ⟨%errs2, Hel2, #Hok2⟩
    (try wp_auto)
    by_cases he2 : sint.Z (W64 0) < sint.Z el2.len
    · simp only [he2, _root_.decide_true]
      wp_auto
      wp_apply wp_ErrorList_ToAggregate_ptr errs_ptr (DFrac.own 1) el2 (DFrac.own 1) errs2
        $$ [$errs $Hel2] as %agg -
      · iexact Hok2
      (try wp_auto)
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      iintro %sla ⟨Hargs, -⟩
      (try wp_auto)
      wp_apply wp_ErrorfAny _ _ _ _ $$ [Hargs] as %ef -
      · iexact Hargs
      (try wp_auto)
      wp_for_post
      iapply HΦ
      iframe
    simp only [he2, _root_.decide_false]
    wp_auto
    wp_apply HgetDesc' as %dsc -
    wp_apply wp_string_len dsc as -
    by_cases hds : sint.Z (W64 1024) < sint.Z (W64 dsc.length)
    · simp only [hds, _root_.decide_true]
      wp_auto
      wp_apply wp_slice_literal
      try (isplitr; (ipureintro; rfl))
      iintro %sla ⟨Hargs, -⟩
      (try wp_auto)
      wp_apply wp_ErrorfAny _ _ _ _ $$ [Hargs] as %ef -
      · iexact Hargs
      (try wp_auto)
      wp_for_post
      iapply HΦ
      iframe
    simp only [hds, _root_.decide_false]
    wp_auto
    wp_for_post
    iframe
    iexists j + W64 1, _, _
    iframe
    ipureintro; constructor <;> word
  · simp only [hlt, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    iframe

end proof

end authorizer
end EtcdGrove
end Perennial
