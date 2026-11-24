/-
The proof of `ConditionsAwareDecisionUnion.Add.spec`
(`Spec/k8s_io/apiserver/pkg/authorization/authorizer/ConditionsAwareDecisionUnion__Add.lean`).
Lean-first (no Rocq counterpart).
-/
module

public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__Add
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__ContainsUnconditionalAllowOrDeny
public import Spec.fmt.ErrorfLeaf
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.SliceRange
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecisionUnion__hasConditionalAuthorizerName
public import Spec.k8s_io.apimachinery.pkg.util.validation.IsDNS1123Subdomain
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__ContainsUnconditionalAllowOrDeny
public import Spec.k8s_io.apimachinery.pkg.util.sets.New
public import Spec.k8s_io.apiserver.pkg.authorization.authorizer.ConditionsAwareDecision__PossibleDecisions
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__UnsortedList
public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Insert
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.PtrMethods
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.PtrMethodsB3
public import Proof.k8s_io.apiserver.pkg.authorization.authorizer.B3Lemmas
public import Proof.k8s_io.apimachinery.pkg.util.sets.PtrMethods

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authorizer

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s_io.apiserver.pkg.authorization.authorizer

/-! The loop spelling out the messages is proved by `wp_slice_for_range_ro`, at the `slice.forRange`
it is about, not unfolded by `wp_auto`. -/
attribute [-instance] pure_wp_slice_for_range

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.authorization.authorizer.Assumptions]

theorem ConditionsAwareDecisionUnion.Add.wp_proof
    (wp_ConditionsAwareDecisionUnion_ContainsUnconditionalAllowOrDeny : EtcdGrove.authorizer.ConditionsAwareDecisionUnion.ContainsUnconditionalAllowOrDeny.spec (GF := GF) (hG := hG))
    (wp_ErrorfLeaf : EtcdGrove.fmt.ErrorfLeaf.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecisionUnion_hasConditionalAuthorizerName : EtcdGrove.authorizer.ConditionsAwareDecisionUnion.hasConditionalAuthorizerName.spec (GF := GF) (hG := hG))
    (wp_IsDNS1123Subdomain : EtcdGrove.validation.IsDNS1123Subdomain.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_ContainsUnconditionalAllowOrDeny : EtcdGrove.authorizer.ConditionsAwareDecision.ContainsUnconditionalAllowOrDeny.spec (GF := GF) (hG := hG))
    (wp_sets_New : EtcdGrove.sets.New.spec (GF := GF) (hG := hG))
    (wp_ConditionsAwareDecision_PossibleDecisions : EtcdGrove.authorizer.ConditionsAwareDecision.PossibleDecisions.spec (GF := GF) (hG := hG))
    (wp_Set__UnsortedList : EtcdGrove.sets.Set.UnsortedList.spec (GF := GF) (hG := hG))
    (wp_Set__Insert : EtcdGrove.sets.Set.Insert.spec (GF := GF) (hG := hG)) :
    ConditionsAwareDecisionUnion.Add.spec (GF := GF) (hG := hG) := by
  intro p ks name d m N
  wp_start as ⟨Hb, #Hd, #Hdn, %Hwf'⟩
  have Hwf : m.WF ∧ m.depth + 1 < 2 ^ 63 := ⟨Hwf'.1, Hwf'.2.1⟩
  have Hname := Hwf'.2.2
  iunfold ownBuilder at Hb
  icases Hb with ⟨%u, %nds, %es, %Hwn, Hp, Hin, Hinc, #HL, Hes, Hesc, #Hest, Hsub, #HN⟩
  obtain ⟨Hwfl, Hnm⟩ := Hwn
  wp_auto
  wp_apply (wp_ConditionsAwareDecisionUnion_ContainsUnconditionalAllowOrDeny p (DFrac.own 1) u)
    $$ [$Hp] as Hp
  iunfold subOk at Hsub
  icases Hsub with ⟨%Hflag, Hset⟩
  rw [Hflag]
  cases hc : Dec.cuadL ks
  · wp_auto
    wp_join iprop(∃ (u' : ConditionsAwareDecisionUnion) (es' : List GoInterface), p ↦ u' ∗
        ⌜u'.inner' = u.inner' ∧
          u'.containsUnconditionalAllowOrDeny' = u.containsUnconditionalAllowOrDeny' ∧
          u'.subDecisionsPossibleDecisions' = u.subDecisionsPossibleDecisions'⌝ ∗
        u'.errs' ↦* es' ∗ ownSliceCap GoInterface u'.errs' (DFrac.own 1) ∗
        unionMap_ptr ↦ p ∗ authorizerName_ptr ↦ name ∗ [∗list] e ∈ es', utilerrors.errTree e) at next
      with [Hp Hes Hesc unionMap authorizerName]
      as ⟨%u1, %es1, Hp, %Hu1, Hes, Hesc, unionMap, authorizerName, #Hest1⟩
    · wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlen
      wp_if_destruct
      · wp_apply (wp_ErrorfLeaf _ slice.nil [] (DFrac.own 1)) as %e1 ⟨-, #He1, %he1⟩
        · isplitr; · iapply ownSlice_nil
          fmt_args_ok
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %osl ⟨Hosl, -⟩
        wp_apply wp_slice_append $$ [$Hes $Hesc $Hosl] as %esl' ⟨Hes, Hesc, -⟩
        isplitr
        · ipureintro; rfl
        iexists _, es ++ [GoInterface.ok e1]
        iframe
        repeat' (first | (ipureintro; simp; done) | isplitr)
        · iexact Hest
        · iapply utilerrors.errTree_of_errOk e1 he1
          iexact He1
        · iapply BigSepL.bigSepL_nil.2; itrivial
      · iframe
        repeat' (first | (ipureintro; simp; done) | isplitr)
        iexact Hest
    obtain ⟨h1, h2, h3⟩ := Hu1
    rw [← h1, ← h3]
    rw [← h2] at Hflag
    wp_join iprop(∃ (u' : ConditionsAwareDecisionUnion) (es' : List GoInterface), p ↦ u' ∗
        ⌜u'.inner' = u1.inner' ∧
          u'.containsUnconditionalAllowOrDeny' = u1.containsUnconditionalAllowOrDeny' ∧
          u'.subDecisionsPossibleDecisions' = u1.subDecisionsPossibleDecisions'⌝ ∗
        u'.errs' ↦* es' ∗ ownSliceCap GoInterface u'.errs' (DFrac.own 1) ∗
        unionMap_ptr ↦ p ∗ authorizerName_ptr ↦ name ∗ u1.inner' ↦* nds ∗
        [∗list] e ∈ es', utilerrors.errTree e) at next
      with [Hp Hes Hesc unionMap authorizerName Hin]
      as ⟨%u2, %es2, Hp, %Hu2, Hes, Hesc, unionMap, authorizerName, Hin, #Hest2⟩
    · wp_apply (wp_ConditionsAwareDecisionUnion_hasConditionalAuthorizerName p (DFrac.own 1) u1
        (DFrac.own 1) nds name) $$ [$Hp $Hin] as %b ⟨Hp, Hin⟩
      wp_if_destruct
      · iframe
        repeat' (first | (ipureintro; simp; done) | isplitr)
        iexact Hest1
      · wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %asl ⟨Hasl, -⟩
        wp_apply (wp_ErrorfLeaf _ _ _ _) $$ [$Hasl] as %e1 ⟨-, #He1, %he1⟩
        · fmt_args_ok
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %osl ⟨Hosl, -⟩
        wp_apply wp_slice_append $$ [$Hes $Hesc $Hosl] as %esl' ⟨Hes, Hesc, -⟩
        isplitr
        · ipureintro; rfl
        iexists _, es1 ++ [GoInterface.ok e1]
        iframe
        repeat' (first | (ipureintro; simp; done) | isplitr)
        · iexact Hest1
        · iapply utilerrors.errTree_of_errOk e1 he1
          iexact He1
        · iapply BigSepL.bigSepL_nil.2; itrivial
    obtain ⟨h1, h2, h3⟩ := Hu2
    rw [← h1, ← h3]
    rw [← h2] at Hflag
    wp_join iprop(∃ (u' : ConditionsAwareDecisionUnion) (es' : List GoInterface), p ↦ u' ∗
        ⌜u'.inner' = u2.inner' ∧
          u'.containsUnconditionalAllowOrDeny' = u2.containsUnconditionalAllowOrDeny' ∧
          u'.subDecisionsPossibleDecisions' = u2.subDecisionsPossibleDecisions'⌝ ∗
        u'.errs' ↦* es' ∗ ownSliceCap GoInterface u'.errs' (DFrac.own 1) ∗
        unionMap_ptr ↦ p ∗ authorizerName_ptr ↦ name ∗ [∗list] e ∈ es', utilerrors.errTree e) at next
      with [Hp Hes Hesc unionMap authorizerName]
      as ⟨%u3, %es3, Hp, %Hu3, Hes, Hesc, unionMap, authorizerName, #Hest3⟩
    · wp_apply (wp_IsDNS1123Subdomain name) as %sl ⟨%ms0, Hms0⟩
      wp_if_destruct
      · -- the messages spelled out, as `%v` prints a `[]string` (without its brackets)
        wp_apply (wp_slice_for_range_ro (V := GoString) _ sl ms0 (DFrac.own 1) _
          (fun _ => iprop(∃ (ms : GoString), msgs_ptr ↦ ms ∗ (∃ x : GoString, e_ptr ↦ x) ∗
            ∃ j : w64, i_ptr ↦ j))) $$ [$Hms0] [msgs e i]
        · iexists _; iframe
        · imodintro
          iintro %j %x %hx ⟨%ms, msgs, ⟨%x0, e⟩, %j0, i⟩ Hms0
          wp_auto
          wp_if_destruct
          · try wp_auto
            isplitr
            · ipureintro; trivial
            iframe
          · try wp_auto
            isplitr
            · ipureintro; trivial
            iframe
        iintro ⟨%ms, msgs, ⟨%x0, e⟩, %j0, i⟩ Hms0
        try wp_auto
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %asl ⟨Hasl, -⟩
        wp_apply (wp_ErrorfLeaf _ _ _ _) $$ [$Hasl] as %e1 ⟨-, #He1, %he1⟩
        · fmt_args_ok
        wp_apply wp_slice_literal
        isplitr
        · ipureintro; rfl
        iintro %osl ⟨Hosl, -⟩
        wp_apply wp_slice_append $$ [$Hes $Hesc $Hosl] as %esl' ⟨Hes, Hesc, -⟩
        isplitr
        · ipureintro; rfl
        iexists _, es2 ++ [GoInterface.ok e1]
        iframe
        repeat' (first | (ipureintro; simp; done) | isplitr)
        · iexact Hest2
        · iapply utilerrors.errTree_of_errOk e1 he1
          iexact He1
        · iapply BigSepL.bigSepL_nil.2; itrivial
      · iframe
        repeat' (first | (ipureintro; simp; done) | isplitr)
        iexact Hest2
    obtain ⟨h1, h2, h3⟩ := Hu3
    rw [← h1, ← h3]
    rw [← h2] at Hflag
    wp_apply (ConditionsAwareDecision.wp_ptr_ContainsUnconditionalAllowOrDeny_of
      wp_ConditionsAwareDecision_ContainsUnconditionalAllowOrDeny d_ptr (DFrac.own 1) d m) $$ [$d]
      as d
    · iexact Hd
    wp_join iprop(∃ (u' : ConditionsAwareDecisionUnion), p ↦ u' ∗
        ⌜u'.inner' = u3.inner' ∧ u'.errs' = u3.errs' ∧
          u'.subDecisionsPossibleDecisions' = u3.subDecisionsPossibleDecisions' ∧
          u'.containsUnconditionalAllowOrDeny' = Bool.or (Dec.cuadL ks) m.cuad⌝ ∗
        unionMap_ptr ↦ p) at next
      with [Hp unionMap]
      as ⟨%u4, Hp, %Hu4, unionMap⟩
    · cases hm : m.cuad
      · wp_auto
        iframe
        ipureintro; simp [Hflag, hc]
      · wp_auto
        iframe
        ipureintro; simp [hc]
    obtain ⟨h1, h2, h3, h4⟩ := Hu4
    rw [← h1, ← h2, ← h3]
    clear Hflag
    wp_apply (wp_slice_literal
      [({ conditionalAuthorizerName' := name, d' := d } : namedConditionsAwareDecision)])
    isplitr
    · ipureintro; rfl
    iintro %osl ⟨Hosl, -⟩
    wp_apply wp_slice_append $$ [$Hin $Hinc $Hosl] as %isl ⟨Hin, Hinc, -⟩
    wp_join iprop(∃ (u' : ConditionsAwareDecisionUnion) (S : GMap w64 sets.Elem), p ↦ u' ∗
        ⌜u'.inner' = isl ∧ u'.errs' = u4.errs' ∧
          u'.containsUnconditionalAllowOrDeny' = u4.containsUnconditionalAllowOrDeny' ∧
          setIs S (Dec.subL ks)⌝ ∗
        u'.subDecisionsPossibleDecisions' ↦$ S ∗ unionMap_ptr ↦ p) at next
      with [Hp unionMap Hset]
      as ⟨%u5, %S, Hp, %Hu5, HS, unionMap⟩
    · icases Hset with (⟨%Hks, %Hnil⟩ | ⟨%S, HS, %HSs⟩)
      · subst Hks
        rw [Hnil]
        wp_auto
        wp_apply (wp_sets_New (K := w64) (T := Decision.ty) slice.nil (DFrac.own 1) []) as %r ⟨HS, -⟩
        · iapply ownSlice_nil
        iframe
        ipureintro
        refine ⟨rfl, rfl, rfl, rfl, ?_⟩
        intro k
        simp [Dec.subL, PD.has_empty, sets.insertAll]
      · ihave %Hnn := ownMap_not_nil _ _ _ $$ HS
        rw [decide_eq_false Hnn]
        wp_auto
        isplitl []
        · ipureintro; rfl
        iexists { u4 with inner' := isl }, S
        iframe
        ipureintro
        exact ⟨rfl, rfl, rfl, HSs⟩
    obtain ⟨h1, h2, h3, hS⟩ := Hu5
    wp_apply (ConditionsAwareDecision.wp_ptr_PossibleDecisions_of
      wp_ConditionsAwareDecision_PossibleDecisions d_ptr (DFrac.own 1) d m) $$ [$d]
      as %sp ⟨⟨%P, HP, %HPm⟩, d⟩
    · iexact Hd
    wp_apply (wp_Set__UnsortedList (K := w64) (T := Decision.ty) sp (DFrac.own 1) P) $$ [$HP]
      as %psl %ps ⟨HP, Hpsl, %Hps⟩
    icases (ConditionsAwareDecisionUnion.ConditionsAwareDecisionUnion_access_load_subDecisionsPossibleDecisions
      p u5 (DFrac.own 1)).access_strict $$ Hp with ⟨Hf, Hclose⟩
    wp_apply (sets.Set.wp_ptr_Insert_of wp_Set__Insert _ (DFrac.own 1) u5.subDecisionsPossibleDecisions' S
      psl (DFrac.own 1) ps) $$ [$Hf $HS $Hpsl] as ⟨Hf, HS, -⟩
    ihave Hp := Hclose $$ Hf
    ihave #HL' := isDecisionL_snoc _ ks d m $$ HL Hd
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    iunfold ownBuilder
    iexists u5, nds ++ [{ conditionalAuthorizerName' := name, d' := d }], es3
    rw [h1, h2]
    iframe
    isplitr
    · ipureintro
      obtain ⟨Hwfl1, Hwfl2⟩ := Hwfl
      obtain ⟨Hwf1, Hwf2⟩ := Hwf
      refine ⟨⟨Dec.WFL_append ks m Hwfl1 Hwf1, by rw [Dec.depthL_append]; omega⟩, fun nd hnd => ?_⟩
      rcases List.mem_append.mp hnd with hnd | hnd
      · exact Hnm nd hnd
      · simp only [List.mem_singleton] at hnd; subst hnd; exact Hname
    isplitr
    · rw [List.map_append, List.map_singleton]; iexact HL'
    isplitr
    · iexact Hest3
    isplitl
    rotate_left
    · rw [List.map_append, List.map_singleton]
      iapply decNamesL_snoc N _ ks d m $$ HN Hdn
    iunfold subOk
    isplitr
    · ipureintro; rw [h3, h4, Dec.cuadL_append]
    iright
    iexists sets.insertAll S ps
    iframe
    ipureintro
    exact setIs_insertAll_b3 S P ks m ps hS HPm Hps.1
  · wp_auto
    iapply HΦ
    simp only [↓reduceIte]
    iunfold ownBuilder
    iexists u, nds, es
    iframe
    iframe #
    isplitr
    · ipureintro; exact ⟨Hwfl, Hnm⟩
    iunfold subOk
    iframe
    ipureintro; rw [Hflag, hc]

end proof

end authorizer
end EtcdGrove
end Perennial
