/-
The proof of `ConditionsAwareDecisionUnion.ToDecision.spec` (`Spec/k8s_io/apiserver/pkg/authorizat
ion/authorizer/ConditionsAwareDecisionUnion__ToDecision.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__ToDecision
public import Spec.k8s_io.apimachinery.pkg.util.errors.NewAggregate
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__FailureDecision
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionFromParts
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__PossibleDecisions
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Len
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__UnsortedList
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.collectReasonsAndErrors
public import Perennial.Spec.strings.Join
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionNoOpinion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionAllow
public import Perennial.Spec.errors.New
public import Spec.slices.Clone
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Clone
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.B3Lemmas
public import Proof.k8s_io.apimachinery.pkg.util.sets.PtrMethods
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.PtrMethodsB3
public import Proof.k8s_io.apimachinery.pkg.util.errors.ErrTreeOk
public import Perennial.Proof.errors.NewVar

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

theorem ConditionsAwareDecisionUnion.ToDecision.wp_proof
    (wp_NewAggregate : EtcdGrove.utilerrors.NewAggregate.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionUnion_FailureDecision : EtcdGrove.authorizer.ConditionsAwareDecisionUnion.FailureDecision.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionFromParts : EtcdGrove.authorizer.ConditionsAwareDecisionFromParts.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionUnion_PossibleDecisions : EtcdGrove.authorizer.ConditionsAwareDecisionUnion.PossibleDecisions.spec (GF := GF) (hG := hG))
    (wp_Set__Len : EtcdGrove.sets.Set.Len.spec (GF := GF) (hG := hG))
    (wp_Set__UnsortedList : EtcdGrove.sets.Set.UnsortedList.spec (GF := GF) (hG := hG))
    (wp_collectReasonsAndErrors : EtcdGrove.authorizer.collectReasonsAndErrors.spec (GF := GF) (hG := hG))
    (wp_Join : _root_.Perennial.strings.Join.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionDeny : EtcdGrove.authorizer.ConditionsAwareDecisionDeny.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionNoOpinion : EtcdGrove.authorizer.ConditionsAwareDecisionNoOpinion.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionAllow : EtcdGrove.authorizer.ConditionsAwareDecisionAllow.spec (GF := GF) (hG := hG))
    (wp_errors_New : _root_.Perennial.errors.New.spec (GF := GF) (hG := hG))
    (wp_Clone : EtcdGrove.slices.Clone.spec (GF := GF) (hG := hG))
    (wp_Set_Clone : EtcdGrove.sets.Set.Clone.spec (GF := GF) (hG := hG)) :
    ConditionsAwareDecisionUnion.ToDecision.spec (GF := GF) (hG := hG) := by
  intro p ks
  wp_start as Hb
  iunfold ownBuilder at Hb
  icases Hb with ⟨%u, %nds, %es, %Hwfl, Hp, Hin, Hinc, #HL, Hes, Hesc, #Hest, Hsub⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hes
  wp_auto
  wp_if_destruct
  rotate_left
  · wp_apply (wp_NewAggregate u.errs' (DFrac.own 1) es) $$ [$Hes] as %agg ⟨Hes, Hagg⟩
    ihave #Hagg := utilerrors.errTreeOrNil_of_newAggregate' es agg $$ [Hagg]
    · isplitr
      · iexact Hest
      · iexact Hagg
    wp_apply (wp_ConditionsAwareDecisionUnion_FailureDecision p (DFrac.own 1) u (DFrac.own 1) ks)
      $$ [$Hp $Hsub] as ⟨Hp, Hsub⟩
    wp_apply (wp_ConditionsAwareDecisionFromParts _ _ _) $$ [] as %dd #Hdd
    · first | iassumption | iapply utilerrors.errTreeOrNil_nil
    iapply HΦ
    isplitl []
    · iunfold isWFDecisionLe
      iexists _
      iframe #
      ipureintro; exact ⟨Dec.ofWord_WF _, by rw [Dec.ofWord_depth]; omega⟩
    iunfold ownBuilder
    iexists u, nds, es
    iframe
    iframe #
    ipureintro; exact Hwfl
  · wp_apply (wp_ConditionsAwareDecisionUnion_PossibleDecisions p (DFrac.own 1) u (DFrac.own 1) ks)
      $$ [$Hp $Hsub] as %sp ⟨⟨%S, HS, %HSp⟩, Hp, Hsub⟩
    wp_apply (sets.Set.wp_ptr_Len_of (K := w64) (T := Decision.ty) wp_Set__Len possibleDecisions_ptr
      (DFrac.own 1) sp (DFrac.own 1) S) $$ [$possibleDecisions $HS] as ⟨possibleDecisions, HS⟩
    have Hsz := setIs_size S _ HSp
    rw [Hsz]
    wp_if_destruct
    rotate_left
    · have hc1 : (Dec.pd (.union ks)).card ≠ 1 := fun h => Hif (by rw [h]; rfl)
      iunfold subOk at Hsub
      icases Hsub with ⟨%Hflag, Hset⟩
      icases Hset with (⟨%Hks, -⟩ | ⟨%S0, HS0, %HS0⟩)
      · subst Hks
        exact absurd rfl hc1
      wp_apply (wp_Clone u.inner' (DFrac.own 1) nds) $$ [$Hin] as %ci ⟨Hin, Hci, -⟩
      imod ownSlice_persist ci (DFrac.own 1) nds $$ Hci with #Hci
      icases (ConditionsAwareDecisionUnion.ConditionsAwareDecisionUnion_access_load_subDecisionsPossibleDecisions
        p u (DFrac.own 1)).access_strict $$ Hp with ⟨Hf, Hclose⟩
      wp_apply +noauto (sets_wp_ptr_Clone_of (K := w64) (T := Decision.ty) wp_Set_Clone _ (DFrac.own 1)
        u.subDecisionsPossibleDecisions' (DFrac.own 1) S0) $$ [$Hf $HS0] as %r ⟨Hf, HS0, Hr⟩
      ihave Hp := Hclose $$ Hf
      imod ownMap_persist r (DFrac.own 1) S0 $$ Hr with #Hr
      wp_auto
      iapply HΦ
      isplitl []
      · iunfold isWFDecisionLe
        iexists Dec.union ks
        isplitl
        · iunfold isDecision
          imodintro
          simp only [isDecisionRaw]
          isplitr
          · ipureintro; trivial
          isplitl
          · iunfold subOk
            isplitr
            · ipureintro; exact Hflag
            iright
            iexists S0
            iframe #
            ipureintro; exact HS0
          isplitl
          · iexists nds
            iframe #
            iunfold isDecisionL at HL
            iexact HL
          · iapply utilerrors.errTreeOrNil_nil
        · ipureintro
          have := Dec.union_card_pos ks
          exact ⟨⟨Hwfl.1, by omega, Hwfl.2⟩, by simp [Dec.depth]⟩
      iunfold ownBuilder
      iexists u, nds, es
      iframe
      iframe #
      isplitr
      · ipureintro; exact Hwfl
      iunfold subOk
      isplitr
      · ipureintro; exact Hflag
      iright
      iexists S0
      iframe
      ipureintro; exact HS0
    · wp_apply (sets_wp_ptr_UnsortedList_of (K := w64) (T := Decision.ty) wp_Set__UnsortedList
        possibleDecisions_ptr (DFrac.own 1) sp (DFrac.own 1) S) $$ [$possibleDecisions $HS]
        as %lsl %lks ⟨possibleDecisions, HS, Hlsl, %Hlks⟩
      have hcard : (Dec.pd (.union ks)).card = 1 := by
        have : (Dec.pd (.union ks)).card ≤ 3 := by
          unfold PD.card; generalize (Dec.pd (.union ks)).deny = a;
          generalize (Dec.pd (.union ks)).allow = b; generalize (Dec.pd (.union ks)).noOpinion = c
          cases a <;> cases b <;> cases c <;> decide
        word
      obtain ⟨k0, hk0⟩ : ∃ k0, lks = [k0] := by
        match lks, Hlks.2.2 with
        | [k0], _ => exact ⟨k0, rfl⟩
        | [], h => rw [Hsz, hcard] at h; cases h
        | _ :: _ :: _, h => rw [Hsz, hcard] at h; simp at h
      subst hk0
      ihave %Hlsl_len := ownSlice_len _ _ _ $$ Hlsl
      have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z lsl.len := by
        obtain ⟨h1, h2⟩ := Hlsl_len
        simp only [List.length_singleton] at h1
        constructor <;> word
      simp only [hb, _root_.and_self, ↓reduceIte]
      wp_apply (wp_load_slice_index lsl (sint.Z (W64 0)) [k0] _ k0 hb.1) $$ [Hlsl] as Hlsl
      · iframe; ipureintro; rfl
      ihave %Hin_len := ownSlice_len _ _ _ $$ Hin
      ihave Hrn : (slice.nil ↦* ([] : List GoString) : IProp GF) $$ []
      · iapply ownSlice_nil
      ihave Hrc : ownSliceCap (GF := GF) GoString slice.nil (DFrac.own 1) $$ []
      · iapply ownSliceCap_nil
      ihave Hen : (slice.nil ↦* ([] : List GoInterface) : IProp GF) $$ []
      · iapply ownSlice_nil
      ihave Hec : ownSliceCap (GF := GF) GoInterface slice.nil (DFrac.own 1) $$ []
      · iapply ownSliceCap_nil
      ihave HI : (∃ (j : w64) (rsl esl : GoSlice) (rxs : List GoString) (eys : List GoInterface)
          (nd : namedConditionsAwareDecision),
          "i" ∷ i_ptr ↦ j ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z u.inner'.len⌝ ∗
          "Hin" ∷ u.inner' ↦* nds ∗
          "aggregateReasons" ∷ aggregateReasons_ptr ↦ rsl ∗ "Hrn" ∷ rsl ↦* rxs ∗
          "Hrc" ∷ ownSliceCap GoString rsl (DFrac.own 1) ∗
          "aggregateErrors" ∷ aggregateErrors_ptr ↦ esl ∗ "Hen" ∷ esl ↦* eys ∗
          "Hec" ∷ ownSliceCap GoInterface esl (DFrac.own 1) ∗
          "#Heys" ∷ ([∗list] e ∈ eys, utilerrors.errTree e) ∗
          "namedDecision" ∷ namedDecision_ptr ↦ nd ∗
          "onlyPossibleDecision" ∷ onlyPossibleDecision_ptr ↦ k0 : IProp GF)
        $$ [i Hin aggregateReasons Hrn Hrc aggregateErrors Hen Hec namedDecision onlyPossibleDecision]
      · iexists W64 0, slice.nil, slice.nil, [], [], _
        iframe
        isplitr
        · ipureintro; constructor <;> word
        iapply BigSepL.bigSepL_nil.2; itrivial
      wp_for HI
      by_cases hlt : sint.Z j < sint.Z u.inner'.len
      · simp only [hlt, _root_.decide_true, ↓reduceIte]
        wp_auto
        obtain ⟨v, hv⟩ : ∃ v, nds[sint.nat j]? = some v :=
          ⟨_, List.getElem?_eq_getElem (by word)⟩
        have hb : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z u.inner'.len := ⟨Hj.1, hlt⟩
        simp only [hb, _root_.and_self, ↓reduceIte]
        wp_apply (wp_load_slice_index u.inner' (sint.Z j) nds _ v Hj.1) $$ [Hin] as Hin
        · iframe; ipureintro; simpa [sint.nat] using hv
        wp_apply (wp_slice_literal [v.conditionalAuthorizerName'])
        isplitr
        · ipureintro; rfl
        iintro %nsl ⟨Hnsl, -⟩
        wp_auto
        have hvd : (List.map (fun x => x.d') nds)[sint.nat j]? = some v.d' := by
          rw [List.getElem?_map, hv]; rfl
        icases isDecisionL_lookup _ ks (sint.nat j) v.d' hvd $$ HL with ⟨%mj, %Hmj, #Hdj⟩
        have Hdep : [v.conditionalAuthorizerName'].length + mj.depth < 2 ^ 63 := by
          have := Dec.depth_le_depthL ks _ mj Hmj
          have := Hwfl.2
          simp only [List.length_singleton]; omega
        wp_apply (wp_collectReasonsAndErrors _ (DFrac.own 1) [v.conditionalAuthorizerName'] v.d' mj k0 Hdep)
          $$ [Hnsl] as %rs %es2 ⟨-, ⟨%xs2, Hrs, -⟩, ⟨%ys2, Hes2, -, #Hys2⟩⟩
        · iframe; iexact Hdj
        wp_apply wp_slice_append $$ [$Hrn $Hrc $Hrs] as %rsl' ⟨Hrn, Hrc, -⟩
        wp_apply wp_slice_append $$ [$Hen $Hec $Hes2] as %esl' ⟨Hen, Hec, -⟩
        wp_for_post
        iframe
        iexists j + W64 1, _, _, _, _, _
        iframe
        isplitr
        · ipureintro; constructor <;> word
        iapply BigSepL.bigSepL_append.2
        isplitr; · iexact Heys
        iexact Hys2
      · simp only [hlt, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
        wp_auto
        wp_if_destruct
        · wp_apply (wp_Join rsl rxs (DFrac.own 1) _) $$ [$Hrn] as Hrn
          wp_apply (wp_NewAggregate esl (DFrac.own 1) eys) $$ [$Hen] as %agg ⟨Hen, Hagg⟩
          ihave #Hagg := utilerrors.errTreeOrNil_of_newAggregate' eys agg $$ [Hagg]
          · isplitr
            · iexact Heys
            · iexact Hagg
          wp_apply (wp_ConditionsAwareDecisionDeny _ _) $$ [] as %dd #Hdd
          · first | iassumption | iapply utilerrors.errTreeOrNil_nil
          iapply HΦ
          isplitl []
          · iunfold isWFDecisionLe
            iexists _
            iframe #
            ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
          iunfold ownBuilder
          iexists u, nds, es
          iframe
          iframe #
          ipureintro; exact Hwfl
        · wp_if_destruct
          · wp_apply (wp_Join rsl rxs (DFrac.own 1) _) $$ [$Hrn] as Hrn
            wp_apply (wp_NewAggregate esl (DFrac.own 1) eys) $$ [$Hen] as %agg ⟨Hen, Hagg⟩
            ihave #Hagg := utilerrors.errTreeOrNil_of_newAggregate' eys agg $$ [Hagg]
            · isplitr
              · iexact Heys
              · iexact Hagg
            wp_apply (wp_ConditionsAwareDecisionNoOpinion _ _) $$ [] as %dd #Hdd
            · first | iassumption | iapply utilerrors.errTreeOrNil_nil
            iapply HΦ
            isplitl []
            · iunfold isWFDecisionLe
              iexists _
              iframe #
              ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
            iunfold ownBuilder
            iexists u, nds, es
            iframe
            iframe #
            ipureintro; exact Hwfl
          · wp_if_destruct
            · wp_apply (wp_Join rsl rxs (DFrac.own 1) _) $$ [$Hrn] as Hrn
              wp_apply (wp_NewAggregate esl (DFrac.own 1) eys) $$ [$Hen] as %agg ⟨Hen, Hagg⟩
              ihave #Hagg := utilerrors.errTreeOrNil_of_newAggregate' eys agg $$ [Hagg]
              · isplitr
                · iexact Heys
                · iexact Hagg
              wp_apply (wp_ConditionsAwareDecisionAllow _ _) $$ [] as %dd #Hdd
              · first | iassumption | iapply utilerrors.errTreeOrNil_nil
              iapply HΦ
              isplitl []
              · iunfold isWFDecisionLe
                iexists _
                iframe #
                ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
              iunfold ownBuilder
              iexists u, nds, es
              iframe
              iframe #
              ipureintro; exact Hwfl
            · wp_apply _root_.Perennial.errors.wp_New_errorString as %ee ⟨#_, #Hee⟩
              ihave #Hee := utilerrors.errorString_errTreeOrNil ee _ $$ Hee
              wp_apply (wp_ConditionsAwareDecisionDeny _ _) $$ [] as %dd #Hdd
              · first | iassumption | iapply utilerrors.errTreeOrNil_nil
              iapply HΦ
              isplitl []
              · iunfold isWFDecisionLe
                iexists _
                iframe #
                ipureintro; exact ⟨trivial, by simp [Dec.depth]⟩
              iunfold ownBuilder
              iexists u, nds, es
              iframe
              iframe #
              ipureintro; exact Hwfl

end proof

end authorizer
end EtcdGrove
end Perennial
