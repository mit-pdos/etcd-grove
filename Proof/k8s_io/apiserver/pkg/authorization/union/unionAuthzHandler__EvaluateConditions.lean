/-
The proof of `unionAuthzHandler.EvaluateConditions.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/union/unionAuthzHandler__EvaluateConditions.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Proof.fmt.OutLemmas
public import Spec.k8s_io.apiserver.pkg.authorization.union.unionAuthzHandler__EvaluateConditions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsUnion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__FailureDecision
public import Perennial.Spec.errors.New
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__UnionedDecisions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsDeny
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__Reason
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__Error
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsAllow
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsNoOpinion
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__IsConditionsMap
public import Spec.k8s_io.apiserver.pkg.authorization.union.unionAuthzHandler__evaluateConditions
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__PossibleDecisions
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Has
public import Spec.k8s_io.apimachinery.pkg.util.sets.ListW
public import Spec.fmt.ErrorfLeaf
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.SliceRange
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.PtrMethodsB1
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.FmtArgs
public import Perennial.Spec.fmt.Sprintf
public import Perennial.Spec.strings.Join
public import Spec.k8s_io.apimachinery.pkg.util.errors.NewAggregate
public import Proof.k8s_io.apiserver.pkg.authorization.union.B5Lemmas
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.B1Lemmas
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.PtrMethods
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.ForRange

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace union

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer k8s_io.apiserver.pkg.authorization.union EtcdGrove.authorizer

/-! The loop spelling out the possible decisions is proved by `wp_slice_for_range_ro`, at the
`slice.forRange` it is about, not unfolded by `wp_auto`. -/
attribute [-instance] pure_wp_slice_for_range

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.union.Assumptions]

theorem unionAuthzHandler.EvaluateConditions.wp_proof
    (wp_ConditionsAwareDecision_IsUnion : EtcdGrove.authorizer.ConditionsAwareDecision.IsUnion.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_FailureDecision : EtcdGrove.authorizer.ConditionsAwareDecision.FailureDecision.spec (GF := GF) (hG := hG))
    (wp_errors_New : _root_.Perennial.errors.New.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_UnionedDecisions : EtcdGrove.authorizer.ConditionsAwareDecision.UnionedDecisions.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsDeny : EtcdGrove.authorizer.ConditionsAwareDecision.IsDeny.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_Reason : EtcdGrove.authorizer.ConditionsAwareDecision.Reason.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_Error : EtcdGrove.authorizer.ConditionsAwareDecision.Error.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsAllow : EtcdGrove.authorizer.ConditionsAwareDecision.IsAllow.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsNoOpinion : EtcdGrove.authorizer.ConditionsAwareDecision.IsNoOpinion.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_IsConditionsMap : EtcdGrove.authorizer.ConditionsAwareDecision.IsConditionsMap.spec (GF := GF) (hG := hG))
    (wp_unionAuthzHandler_evaluateConditions : EtcdGrove.union.unionAuthzHandler.evaluateConditions.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_PossibleDecisions : EtcdGrove.authorizer.ConditionsAwareDecision.PossibleDecisions.spec (GF := GF) (hG := hG))
    (wp_Set__Has : EtcdGrove.sets.Set.Has.spec (GF := GF) (hG := hG))
    (wp_List : EtcdGrove.sets.List'.specW (GF := GF) (hG := hG))
    (wp_ErrorfLeaf : EtcdGrove.fmt.ErrorfLeaf.spec (GF := GF) (hG := hG))
    (wp_Sprintf : _root_.Perennial.fmt.Sprintf.spec (GF := GF) (hG := hG))
    (wp_Join : _root_.Perennial.strings.Join.spec (GF := GF) (hG := hG))
    (wp_NewAggregate : EtcdGrove.utilerrors.NewAggregate.spec (GF := GF) (hG := hG))
    (wp_Decision_String : EtcdGrove.authorizer.Decision.String.spec (GF := GF) (hG := hG)) :
    unionAuthzHandler.EvaluateConditions.spec (GF := GF) (hG := hG) := by
  intro h ctx d m data
  wp_start as ⟨#Hu, #Hd, %Hwf', #Hdn⟩
  have Hwf := Hwf'.1
  have Hfit := Hwf'.2
  wp_auto
  wp_apply (wp_ptr_IsUnion_of wp_ConditionsAwareDecision_IsUnion) $$ [$unevaluatedDecision] as unevaluatedDecision
  icases isDecision_tag d m $$ Hd with %Htag
  rw [Htag, Dec.tag_union]
  cases m with
  | union ks =>
    simp only [Dec.isUnion]
    icases isDecision_union_names authzNameMax d ks $$ Hd Hdn with ⟨%nds, #Hnds, #HL, %Hnm, #HN⟩
    wp_auto
    wp_apply (wp_ptr_UnionedDecisions_of wp_ConditionsAwareDecision_UnionedDecisions)
      $$ [$unevaluatedDecision] as %f ⟨#Hf, unevaluatedDecision⟩
    · iexact Hnds
    (try wp_auto)
    wp_bind (App (App (Val (func.forRange 2)) _) _)
    iapply wp_post_named
    iintro %K %hK
    iapply k8s.wp_forRange2 _ _ _ (by simp) rfl
    iintro %y %Tok %Done HTok #Hy
    iunfold seq2Ok at Hf
    ispecialize Hf $$ %y
      %(fun i => iprop(Tok ∗ ∃ (sd : ConditionsAwareDecision) (nm : GoString) (rl el : GoSlice)
        (rls : List GoString) (els : List GoInterface),
        unevaluatedSubDecision_ptr ↦ sd ∗ currentAuthorizerName_ptr ↦ nm ∗
        reasonlist_ptr ↦ rl ∗ rl ↦* rls ∗ ownSliceCap GoString rl (DFrac.own 1) ∗
        errlist_ptr ↦ el ∗ el ↦* els ∗ ownSliceCap GoInterface el (DFrac.own 1) ∗
        «$res0_ptr» ↦ zero_val w64 ∗ «$res1_ptr» ↦ zero_val GoString ∗ «$res2_ptr» ↦ GoInterface.nil ∗
        authzHandler_ptr ↦ h ∗ data_ptr ↦ data ∗ ctx_ptr ↦ ctx ∗
        (∀ (dec : w64) (r : GoString) (e : GoInterface),
          ⌜(Dec.union ks).pd.has dec = true ∨ dec = (Dec.union ks).pd.failure⌝ -∗ Φ (PairV (PairV #dec #r) #e)) ∗
        ⌜∀ j k, j < i → ks[j]? = some k → k.cuad = false⌝ ∗
        ⌜rls.length ≤ i ∧ ∀ x ∈ rls, x.length ≤ (authzNameMax + 2 + maxAddr.toNat)⌝))
      %(iprop(∃ r, Done (returnVal r) ∗ K (returnVal r)))
    iunfold iterRunOk at Hf
    ihave %Hlen := isDecisionL_length $$ HL
    simp only [List.length_map] at Hlen
    iapply Hf $$ [] [HTok HΦ «$res0» «$res1» «$res2» reasonlist errlist unevaluatedSubDecision
      currentAuthorizerName authzHandler data ctx]
    · -- a child
      iintro !> %i %k %v %Hi
      iunfold yield2Ok
      iintro %Ψ !> HI HΨ
      simp only
      icases HI with ⟨HTok, %sd, %nm, %rl, %el, %rls, %els, unevaluatedSubDecision, currentAuthorizerName,
        reasonlist, Hrl, Hrlc, errlist, Hel, Helc, «$res0», «$res1», «$res2», authzHandler, data, ctx, HΦ,
        %Hcuad, %Hrls⟩
      have Hkn : k.length ≤ authzNameMax := by
        rw [List.getElem?_map] at Hi
        cases hnd : nds[i]? with
        | none => rw [hnd] at Hi; simp at Hi
        | some nd =>
          rw [hnd] at Hi
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at Hi
          rw [← Hi.1]; exact Hnm nd (List.mem_of_getElem? hnd)
      have Hv : (nds.map (·.d'))[i]? = some v := by
        rw [List.getElem?_map] at Hi ⊢
        cases hnd : nds[i]? with
        | none => rw [hnd] at Hi; simp at Hi
        | some nd => rw [hnd] at Hi; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at Hi ⊢; exact Hi.2
      icases isDecisionL_lookup _ ks i v Hv $$ HL with ⟨%mk, %Hmk, #Hv⟩
      have Hmkwf : mk.WF := Dec.WFL_get ks i mk Hwf.1 Hmk
      have Hmkin : mk ∈ ks := List.mem_of_getElem? Hmk
      icases isDecision_tag v mk $$ Hv with %Hvtag
      iapply Hy $$ %_ %_ %_ [] HTok
      · ipureintro; exact ⟨by simp, by simp⟩
      wp_auto
      wp_apply (wp_ptr_IsDeny_of wp_ConditionsAwareDecision_IsDeny) $$ [$unevaluatedSubDecision]
        as unevaluatedSubDecision
      rw [Hvtag, Dec.tag_deny]
      cases mk
      case deny =>
        simp only [Dec.isDeny]
        wp_auto
        wp_apply (wp_ptr_Reason_of wp_ConditionsAwareDecision_Reason) $$ [$unevaluatedSubDecision]
          as unevaluatedSubDecision
        wp_apply (wp_ptr_Error_of wp_ConditionsAwareDecision_Error) $$ [$unevaluatedSubDecision]
          as unevaluatedSubDecision
        (try wp_auto)
        unfold k8s.forRangePost
        iright
        isplitr
        · ipureintro; exact Or.inr ⟨_, rfl, by simp⟩
        iintro HD
        iapply HΨ
        simp only [Bool.false_eq_true, ↓reduceIte]
        iexists #()
        iframe HD
        rw [hK]; simp only []
        wp_auto
        iapply HΦ; ipureintro; left; rw [PD.has_zero]; exact Dec.pd_child_deny ks _ Hmkin rfl
      case allow =>
        simp only [Dec.isDeny]
        wp_auto
        wp_apply (ConditionsAwareDecision.wp_ptr_IsAllow_of wp_ConditionsAwareDecision_IsAllow) $$ [$unevaluatedSubDecision]
          as unevaluatedSubDecision
        rw [Hvtag, Dec.tag_allow]
        simp only [Dec.isAllow]
        wp_auto
        wp_apply (wp_ptr_Reason_of wp_ConditionsAwareDecision_Reason) $$ [$unevaluatedSubDecision]
          as unevaluatedSubDecision
        wp_apply (wp_ptr_Error_of wp_ConditionsAwareDecision_Error) $$ [$unevaluatedSubDecision]
          as unevaluatedSubDecision
        (try wp_auto)
        unfold k8s.forRangePost
        iright
        isplitr
        · ipureintro; exact Or.inr ⟨_, rfl, by simp⟩
        iintro HD
        iapply HΨ
        simp only [Bool.false_eq_true, ↓reduceIte]
        iexists #()
        iframe HD
        rw [hK]; simp only []
        wp_auto
        iapply HΦ; ipureintro; left; rw [PD.has_one]; exact Dec.pd_child_allow ks _ Hmkin rfl
      case' noOpinion =>
        simp only [Dec.isDeny]
        wp_auto
        wp_apply (ConditionsAwareDecision.wp_ptr_IsAllow_of wp_ConditionsAwareDecision_IsAllow) $$ [$unevaluatedSubDecision]
          as unevaluatedSubDecision
        rw [Hvtag, Dec.tag_allow]
        simp only [Dec.isAllow]
        wp_auto
        wp_apply (wp_ptr_IsNoOpinion_of wp_ConditionsAwareDecision_IsNoOpinion) $$ [$unevaluatedSubDecision]
          as unevaluatedSubDecision
        rw [Hvtag, Dec.tag_noOpinion]
        simp only [Dec.isNoOpinion]
        wp_auto
        wp_apply (wp_ptr_Reason_of wp_ConditionsAwareDecision_Reason) $$ [$unevaluatedSubDecision]
          as unevaluatedSubDecision
        wp_apply (wp_ptr_Error_of wp_ConditionsAwareDecision_Error) $$ [$unevaluatedSubDecision]
          as unevaluatedSubDecision
        (try wp_auto)
        generalize v.err' = e0
        generalize v.reason' = r0
      case' cmap | union =>
        simp only [Dec.isDeny]
        wp_auto
        wp_apply (ConditionsAwareDecision.wp_ptr_IsAllow_of wp_ConditionsAwareDecision_IsAllow) $$ [$unevaluatedSubDecision]
          as unevaluatedSubDecision
        rw [Hvtag, Dec.tag_allow]
        simp only [Dec.isAllow]
        wp_auto
        wp_apply (wp_ptr_IsNoOpinion_of wp_ConditionsAwareDecision_IsNoOpinion) $$ [$unevaluatedSubDecision]
          as unevaluatedSubDecision
        rw [Hvtag, Dec.tag_noOpinion]
        simp only [Dec.isNoOpinion]
        wp_auto
        wp_apply (wp_ptr_IsUnion_of wp_ConditionsAwareDecision_IsUnion) $$ [$unevaluatedSubDecision]
          as unevaluatedSubDecision
        rw [Hvtag, Dec.tag_union]
        simp only [Dec.isUnion]
        wp_auto
      case' cmap =>
        wp_apply (wp_ptr_IsConditionsMap_of wp_ConditionsAwareDecision_IsConditionsMap) $$ [$unevaluatedSubDecision]
          as unevaluatedSubDecision
        rw [Hvtag, Dec.tag_cmap]
        simp only [Dec.isCMap]
        wp_auto
      case' cmap | union =>
        wp_apply (wp_ptr_evaluateConditions_of wp_unionAuthzHandler_evaluateConditions) $$ [$authzHandler]
          as %dw %rr %ee authzHandler
        · iframe #
          unfold isWFDecisionFit
          iexists _
          iframe #
          isplitr
          · ipureintro; exact ⟨Hmkwf, Dec.foldFits_child _ ks i _ Hmk Hfit⟩
          iapply decNamesL_lookup _ _ ks i v _ Hv Hmk
          iexact HN
        (try wp_auto)
        -- the guard: an impossible decision becomes the child's failure decision
        wp_bind (If _ _ _)
        iapply (wp_wand (Φ := fun bv => iprop(⌜bv = executeVal⌝ ∗ ∃ (dw' : w64) (r' : GoString) (e' : GoInterface),
            decision_ptr ↦ dw' ∗ reason_ptr ↦ r' ∗ err_ptr ↦ e' ∗ unevaluatedSubDecision_ptr ↦ v ∗
            ⌜∀ m' : Dec, ks[i]? = some m' → m'.pd.has dw' = true⌝))) $$ [decision reason err unevaluatedSubDecision]
        · wp_apply (ConditionsAwareDecision.wp_ptr_PossibleDecisions_of wp_ConditionsAwareDecision_PossibleDecisions)
            $$ [$unevaluatedSubDecision] as %s ⟨⟨%S, HS, %HSm⟩, unevaluatedSubDecision⟩
          · iexact Hv
          (try wp_auto)
          wp_apply (wp_Set__Has s (DFrac.own 1) S dw) $$ [$HS] as HS
          rw [HSm dw]
          cases Hhas : (Dec.pd _).has dw
          · wp_auto
            -- the possible decisions spelled out, as `%v` prints a `[]Decision` (without its brackets)
            wp_apply (ConditionsAwareDecision.wp_ptr_PossibleDecisions_of wp_ConditionsAwareDecision_PossibleDecisions)
              $$ [$unevaluatedSubDecision] as %s2 ⟨⟨%S2, HS2, %HSm2⟩, unevaluatedSubDecision⟩
            · iexact Hv
            (try wp_auto)
            wp_apply (wp_List s2 (DFrac.own 1) S2 (EtcdGrove.authorizer.setIs_size_le_b1 HSm2)) $$ [$HS2] as %sl %dws ⟨HS2, Hsl, -⟩
            (try wp_auto)
            wp_apply (wp_slice_for_range_ro (V := w64) _ sl dws (DFrac.own 1) _
              (fun _ => iprop(∃ (ps : GoString), possible_ptr ↦ ps ∗ (∃ x : w64, p_ptr ↦ x) ∗
                ∃ j : w64, i_ptr ↦ j))) $$ [$Hsl] [possible p i]
            · iexists _; iframe
            · imodintro
              iintro %j %x %hx ⟨%ps, possible, ⟨%x0, p⟩, %j0, i⟩ Hsl
              wp_auto
              wp_if_destruct
              · wp_apply (EtcdGrove.authorizer.Decision.wp_ptr_String_of wp_Decision_String p_ptr (DFrac.own 1) _) $$ [$p] as %str Hp
                try wp_auto
                isplitr
                · ipureintro; rfl
                iframe
              · wp_apply (EtcdGrove.authorizer.Decision.wp_ptr_String_of wp_Decision_String p_ptr (DFrac.own 1) _) $$ [$p] as %str Hp
                try wp_auto
                isplitr
                · ipureintro; rfl
                iframe
            iintro ⟨%ps, possible, ⟨%x0, p⟩, %j0, i⟩ Hsl
            (try wp_auto)
            wp_apply (ConditionsAwareDecision.wp_ptr_FailureDecision_of wp_ConditionsAwareDecision_FailureDecision)
              $$ [$unevaluatedSubDecision] as unevaluatedSubDecision
            · iexact Hv
            (try wp_auto)
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %sp ⟨Hs, -⟩
            (try wp_auto)
            wp_apply wp_ErrorfLeaf $$ [$Hs] as %ferr ⟨Hs, -⟩
            · fmt_args_intro
              isplitl
              · iapply fmt.argOkAt_of_base
                iapply (authorizer.Decision.argOkAtBase wp_Decision_String dw ⟨by decide, rfl, by decide⟩)
                iPkgInit
              isplitl
              · iapply fmt.argOkAt_of_base; simp only [fmt.argOkAtBase]; ileft; ipureintro
                exact (show _root_.Perennial.fmt.ArgsWf [interface.mkOk go.string #ps] from
                  .cons_string _ _ .nil) _ (List.mem_singleton_self _)
              · itrivial
            (try wp_auto)
            iframe
            ipureintro
            refine ⟨rfl, fun m' hm' => ?_⟩; rw [Hmk] at hm'; cases hm'; exact Dec.failure_mem _ Hmkwf rfl
          · wp_auto
            iframe
            ipureintro
            refine ⟨rfl, fun m' hm' => ?_⟩; rw [Hmk] at hm'; cases hm'; exact Hhas
        iintro %bv ⟨%Hbv, %dw', %r0, %e0, decision, reason, err, unevaluatedSubDecision, %Hdw⟩
        subst Hbv
        have Hdw' := Hdw _ Hmk
        rcases PD.has_valid _ _ Hdw' with rfl | rfl | rfl
        · (try wp_auto)
          unfold k8s.forRangePost
          iright
          isplitr
          · ipureintro; exact Or.inr ⟨_, rfl, by simp⟩
          iintro HD
          iapply HΨ
          simp only [Bool.false_eq_true, ↓reduceIte]
          iexists #()
          iframe HD
          rw [hK]; simp only []
          wp_auto
          iapply HΦ; ipureintro; left; rw [PD.has_zero]
          exact Dec.pd_child_deny ks _ Hmkin (by rw [PD.has_zero] at Hdw'; exact Hdw')
        · (try wp_auto)
          unfold k8s.forRangePost
          iright
          isplitr
          · ipureintro; exact Or.inr ⟨_, rfl, by simp⟩
          iintro HD
          iapply HΨ
          simp only [Bool.false_eq_true, ↓reduceIte]
          iexists #()
          iframe HD
          rw [hK]; simp only []
          wp_auto
          iapply HΦ; ipureintro; left; rw [PD.has_one]
          exact Dec.pd_child_allow ks _ Hmkin (by rw [PD.has_one] at Hdw'; exact Hdw')
        (try wp_auto)
      all_goals
        -- the error, appended to `errlist` unless `nil`
        wp_bind (If _ _ _)
        iapply (wp_wand (Φ := fun bv => iprop(⌜bv = executeVal⌝ ∗ ∃ (el' : GoSlice) (els' : List GoInterface),
            errlist_ptr ↦ el' ∗ el' ↦* els' ∗ ownSliceCap GoInterface el' (DFrac.own 1)))) $$ [errlist Hel Helc err]
        · cases e0 with
          | nil =>
            wp_auto
            iframe
            ipureintro; rfl
          | ok ei =>
            wp_auto
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %sp ⟨Hs, -⟩
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Hel $Helc $Hs] as %el' ⟨Hel, Helc, -⟩
            (try wp_auto)
            iframe
            ipureintro; rfl
        iintro %bv ⟨%Hbv, %el', %els', errlist, Hel, Helc⟩
        subst Hbv
        wp_auto
        -- the reason, appended to `reasonlist` unless empty
        wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len_maxAddr as %Hrl0
        wp_bind (If _ _ _)
        iapply (wp_wand (Φ := fun bv => iprop(⌜bv = executeVal⌝ ∗ ∃ (rl' : GoSlice) (rls' : List GoString),
            reasonlist_ptr ↦ rl' ∗ rl' ↦* rls' ∗ ownSliceCap GoString rl' (DFrac.own 1) ∗
            currentAuthorizerName_ptr ↦ k ∗
            ⌜rls'.length ≤ rls.length + 1 ∧ ∀ x ∈ rls', x.length ≤ (authzNameMax + 2 + maxAddr.toNat)⌝))) $$ [reasonlist Hrl Hrlc reason currentAuthorizerName]
        · wp_if_destruct
          · iframe
            ipureintro; exact ⟨by omega, Hrls.2⟩
          · (try wp_auto)
            wp_apply (wp_slice_literal (l := [interface.mkOk go.string #k, interface.mkOk go.string #r0]))
            isplitr
            · ipureintro; rfl
            iintro %sp ⟨Hs, -⟩
            (try wp_auto)
            wp_apply (EtcdGrove.fmt.wp_Sprintf_pure wp_Sprintf go!"%s: %s" [.dir none _root_.Perennial.fmt.verb_s, .lit go!": ", .dir none _root_.Perennial.fmt.verb_s]
              _ [interface.mkOk go.string #k, interface.mkOk go.string #r0] _ (DFrac.own 1)
              (by fmt_encode) (by fmt_fits) (.str _ _ _ (.str _ _ _ .nil))) $$ [$Hs] as %str ⟨Hs, %Hstr⟩
            (try wp_auto)
            wp_apply wp_slice_literal
            isplitr
            · ipureintro; rfl
            iintro %sp' ⟨Hs', -⟩
            (try wp_auto)
            wp_apply wp_slice_append $$ [$Hrl $Hrlc $Hs'] as %rl' ⟨Hrl, Hrlc, -⟩
            (try wp_auto)
            iframe
            ipureintro
            refine ⟨rfl, by simp, ?_⟩
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact Hrls.2 x hx
            · simp only [List.mem_singleton] at hx
              subst hx; rw [Hstr]
              have := authorizer.length_le_maxAddr_toNat r0 Hrl0
              simp only [_root_.Perennial.fmt.render, EtcdGrove.fmt.dirOutFn_str_s, List.length_append,
                List.append_nil, List.length_cons, List.length_nil]
              omega
        iintro %bv ⟨%Hbv, %rl', %rls', reasonlist, Hrl, Hrlc, currentAuthorizerName, %Hrls'⟩
        subst Hbv
        (try wp_auto)
        -- on to the next child
        unfold k8s.forRangePost
        ileft
        isplitr
        · ipureintro; exact Or.inl rfl
        iintro HTok
        iapply HΨ
        simp only [↓reduceIte]
        iframe HTok
        iexists v, k, rl', el', rls', els'
        iframe
        ipureintro
        refine ⟨?_, by omega, Hrls'.2⟩
        refine cuad_step ks i _ Hcuad Hmk ?_
        first
          | rfl
          | exact Bool.eq_false_iff.mpr (fun hc => by
              have h2 := Dec.not_noOpinion_of_cuad _ hc
              rw [PD.has_two, h2] at Hdw'
              cases Hdw')
    · -- the state before the first child
      simp only
      iframe HTok
      iexists _, _, _, _, [], []
      iframe
      isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSliceCap_nil
      isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSliceCap_nil
      ipureintro
      refine ⟨fun j k hj => by omega, by simp, by simp⟩
    · -- after the loop
      iintro !> HI
      isplitr
      · ipureintro; simp
      icases HI with (⟨HTok, %sd, %nm, %rl, %el, %rls, %els, unevaluatedSubDecision, currentAuthorizerName,
        reasonlist, Hrl, Hrlc, errlist, Hel, Helc, «$res0», «$res1», «$res2», authzHandler, data, ctx, HΦ,
        %Hcuad, %Hrls⟩ | HD)
      · ileft
        iframe HTok
        rw [hK]
        simp only []
        wp_auto
        have Hn : rls.length * ((authzNameMax + 2 + maxAddr.toNat) + (go!"\n").length) < _root_.Perennial.strings.joinMax := by
          have h1 := Dec.length_le_sizeL ks
          try simp only [List.length_map] at Hrls
          unfold Dec.foldFits Dec.foldBound at Hfit
          simp only [Dec.size, Dec.depth] at Hfit
          have h2 : rls.length ≤ Dec.sizeL ks + 1 := by omega
          have h3 : (authzNameMax + 2 + maxAddr.toNat) + (go!"\n").length ≤
              (Dec.depthL ks + 1 + 1) * (authzNameMax + 2) + maxAddr.toNat + 6 := by
            have := Nat.le_mul_of_pos_left (authzNameMax + 2) (show 0 < Dec.depthL ks + 1 + 1 by omega)
            simp only [List.length_cons, List.length_nil]
            omega
          exact Nat.lt_of_le_of_lt (Nat.mul_le_mul h2 h3) Hfit
        wp_apply (_root_.Perennial.strings.Join_bounded_of wp_Join rl rls (DFrac.own 1) _ _ Hrls.2 Hn)
          $$ [$Hrl] as Hrl
        (try wp_auto)
        wp_apply wp_NewAggregate $$ [$Hel] as %agg Hel
        (try wp_auto)
        iapply HΦ
        ipureintro
        left
        rw [PD.has_two]
        apply Dec.noOpinion_of_not_cuad
        intro k hk
        obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hk
        exact Hcuad j k (by simp only [List.length_map]; omega) (by rw [List.getElem?_eq_getElem hj, hjk])
      · iright; iright
        iexact HD
  | _ =>
    simp only [Dec.isUnion]
    wp_auto
    wp_apply (ConditionsAwareDecision.wp_ptr_FailureDecision_of wp_ConditionsAwareDecision_FailureDecision)
      $$ [$unevaluatedDecision] as unevaluatedDecision
    · iexact Hd
    (try wp_auto)
    wp_apply wp_errors_New as %err -
    (try wp_auto)
    iapply HΦ
    ipureintro; exact Or.inr rfl

end proof

end union
end EtcdGrove
end Perennial
