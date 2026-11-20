/-
`typed.compareWalker.compare`: a member of the recursion cluster `typed.compareWalkerRec` (`compareWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `compareWalker__compareBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__compareBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Atom__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Schema__Resolve
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.ValidationErrors__WithLazyPrefix
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.deduceAtom
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.handleAtom
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__doScalar
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBRecon
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : typed.Assumptions]

set_option synthInstance.maxHeartbeats 200000 in
set_option synthInstance.maxSize 4096 in
theorem typed.compareWalker.compare.wp_proofBody
    (h_Set_Insert : fieldpath.Set.Insert.spec (GF := GF))
    (h_Atom_Equals : schema.Atom.Equals.spec (GF := GF))
    (h_Schema_Resolve : schema.Schema.Resolve.spec (GF := GF))
    (h_ValidationErrors_WithLazyPrefix : typed.ValidationErrors.WithLazyPrefix.spec (GF := GF))
    (h_deduceAtom : typed.deduceAtom.spec (GF := GF))
    (h_handleAtom : typed.handleAtom.spec (GF := GF))
    (h_compareWalker_doScalar : typed.compareWalker.doScalar.spec (GF := GF)) :
    typed.compareWalker.compare.specBody (GF := GF) := by
  unfold typed.compareWalker.compare.specBody typed.compareWalkerRec.specI
    typed.compareWalker.compare.specI typed.compareWalker.compareListItem.specI
    typed.compareWalker.doList.specI typed.compareWalker.doMap.specI
    typed.compareWalker.visitListItems.specI typed.compareWalker.visitMapItem.specI
    typed.compareWalker.visitMapItems.specI
  iintro #IH
  iintro %w %sc %S %st %c %C %dql %dqr %l %r %f %sp
  wp_start as ⟨Hown, Hl, Hr, %Hpre⟩
  iunfold cwOwn at Hown
  icases Hown with ⟨%ps, Hcore, Hp, Hsp, Ha, Hc⟩
  iunfold cwCore at Hcore
  icases Hcore with ⟨%tr, Hw, #Htr, #Hsc, %Hwf⟩
  ihave ⟨Hl, %Hln⟩ := isValO_nil $$ Hl
  ihave ⟨Hr, %Hrn⟩ := isValO_nil $$ Hr
  wp_auto
  wp_join at (if: _ then _ else _) with [Hl Hr w Hw]
  · rcases l with _ | x
    · rcases r with _ | y
      · simp at Hpre
      · ihave ⟨Hr, %Hrp⟩ := isValO_some $$ Hr
        obtain ⟨pr, Hpr⟩ := Hrp
        rw [Hln.2 rfl, Hpr]
        wp_auto
        wp_join_done
    · ihave ⟨Hl, %Hlp⟩ := isValO_some $$ Hl
      obtain ⟨pl, Hpl⟩ := Hlp
      rw [Hpl]
      wp_auto
      wp_join_done
  have hfind : (S.find st.t.name).isSome := by
    rcases Hpre.1 with h | h
    · obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.1 h
      exact LawB.confO_find S st.t x Hpre.2.1
    · obtain ⟨y, rfl⟩ := Option.isSome_iff_exists.1 h
      exact LawB.confO_find S st.t y Hpre.2.2.1
  obtain ⟨At, hA⟩ := Option.isSome_iff_exists.1 hfind
  have Hnd := Schema.WF_types_nodup_law_holds S Hwf
  ihave #Htr' := (isTypeRefOpt_some_law_holds tr st.t).2 $$ Htr
  wp_apply h_Schema_Resolve sc S tr (some st.t) $$ [] as %atm %ok ⟨%Hok, #Hat⟩
  · iframe #; ipureintro; exact Hnd
  simp only [Schema.resolveRef, Schema.resolvesRef, Schema.resolves, hA, Option.isSome_some] at Hok ⊢
  subst Hok
  wp_auto
  wp_apply h_deduceAtom atm At st.lhs dql l $$ [Hl] as Hl
  · iframe #; iframe
  wp_apply h_deduceAtom atm At st.rhs dqr r $$ [Hr] as Hr
  · iframe #; iframe
  ihave #Hah : atomHandlerOk At atm (go.GoType.PointerType typed.compareWalker.ty) #w
      iprop(cwOwn w sc S st c C sp ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r)
      (fun errs => iprop(noErrs errs ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗
        (∃ sp' : Loc, cwOwn w sc S { st with inLeaf := leafAt S st.t l r } c
          (C.union (cmpBelow S st.t st.path l r)) sp' ∗ ⌜sp ≠ null → sp' = sp⌝))) $$ []
  · icases IH with ⟨-, -, #HdL, #HdM, -, -, -⟩
    cases At with
    | scalar sk =>
      simp only [atomHandlerOk]
      icases (isAtomOpt_scalar_law_holds atm sk).1 $$ Hat with ⟨#Hs, -⟩
      imodintro
      iintro %Φ2 ⟨Hown, Hl, Hr⟩ HΦ2
      wp_apply h_compareWalker_doScalar w sc S st c C dql dqr l r atm.Scalar' sk sp $$ [Hown Hl Hr]
        as %errs ⟨Herrs, Hl, Hr, Hown⟩
      · iframe #; iframe; ipureintro
        exact ⟨hA, Hpre⟩
      iapply HΦ2
      rw [LawB.leafAt_scalar S st.t sk l r hA]
      iframe Herrs Hl Hr
      iexists sp
      iframe Hown
      ipureintro; intro _; rfl
    | list e rel ks =>
      simp only [atomHandlerOk]
      icases (isAtomOpt_list_law_holds atm e rel ks).1 $$ Hat with ⟨-, #Hli⟩
      imodintro
      iintro %Φ2 ⟨Hown, Hl, Hr⟩ HΦ2
      wp_apply HdL $$ [Hown Hl Hr] as %errs HQ
      · iframe #; iframe; ipureintro; exact ⟨hA, Hpre⟩
      iapply HΦ2 $$ HQ
    | map fs e rel =>
      simp only [atomHandlerOk]
      icases (isAtomOpt_map_law_holds atm fs e rel).1 $$ Hat with ⟨-, #Hma⟩
      imodintro
      iintro %Φ2 ⟨Hown, Hl, Hr⟩ HΦ2
      wp_apply HdM $$ [Hown Hl Hr] as %errs HQ
      · iframe #; iframe; ipureintro; exact ⟨hA, Hpre⟩
      iapply HΦ2 $$ HQ
  rcases r with _ | y
  · rcases l with _ | x
    · simp at Hpre
    ihave ⟨Hl, %Hlp⟩ := isValO_some $$ Hl
    obtain ⟨pl, Hpl⟩ := Hlp
    rw [Hrn.2 rfl]
    wp_auto
    ihave Hown : cwOwn w sc S st c C sp $$ [Hw Hp Hsp Ha Hc]
    · unfold cwOwn cwCore
      rw [Hrn.2 rfl]
      iexists ps
      iframe
      iframe #
      ipureintro; exact Hwf
    wp_apply h_handleAtom atm At tr (go.GoType.PointerType typed.compareWalker.ty) #w
      iprop(cwOwn w sc S st c C sp ∗ isValO st.lhs dql (some x) ∗ isValO GoInterface.nil dqr none)
      (fun errs => iprop(noErrs errs ∗ isValO st.lhs dql (some x) ∗ isValO GoInterface.nil dqr none ∗
        (∃ sp' : Loc, cwOwn w sc S (CWSt.mk st.lhs GoInterface.nil st.t st.path (leafAt S st.t (some x) none) st.alloc) c
          (C.union (cmpBelow S st.t st.path (some x) none)) sp' ∗ ⌜sp ≠ null → sp' = sp⌝)))
      $$ [Hown Hl Hr] as %errs' HQ
    · iframe #; iframe

    icases HQ with ⟨Hes, Hl, Hr, %sp', Hown, %Hsp'⟩
    simp only [noErrs, ownErrs]
    icases Hes with ⟨Hes, Hcap⟩
    wp_apply (wp_slice_append (V := typed.ValidationError) slice.nil [] errs' [] (DFrac.own 1))
      $$ [Hes] as %e2 ⟨He2, Hcap2, -⟩
    · iframe
      isplitl
      · iapply ownSlice_nil
      · iapply ownSliceCap_nil
    simp only [List.append_nil]
    iunfold cwOwn at Hown
    icases Hown with ⟨%ps', Hcore, Hp, Hsp, Ha, Hc⟩
    iunfold cwCore at Hcore
    icases Hcore with ⟨%tr', Hw, #Htr', #Hsc', %Hwf'⟩
    have hres := cmpO_below_resolved S st.t st.path (some x) none hfind
    wp_auto
    iclear IH
    simp only
    rw [Hpl]
    cases hlf : leafAt S st.t (some x) none
    · rw [hlf] at hres
      have hC := LawB.cmp_node_removed C (cmpBelow S st.t st.path (some x) none) st.path x
      simp only [Bool.false_eq_true, ↓reduceIte] at hres
      rw [← hres] at hC
      unfold ownCmp; icases Hc with ⟨%rm, %md, %ad, Hcs, Hrm, Hmd, Had⟩
      unfold ownPath; icases Hp with ⟨Hpf, Hpcap⟩
      wp_auto
      have hcard : (C.union (cmpBelow S st.t st.path (some x) none)).removed.CardLt (2 ^ 63 - 1) := by
        have := Hpre.2.2.2.2.1
        rw [hC] at this
        exact LawB.cardLt_union_left _ _ _ this
      wp_apply h_Set_Insert rm _ ps' (DFrac.own 1) st.path $$ [Hrm Hpf] as ⟨Hrm, Hpf⟩
      · iframe; ipureintro; exact hcard
      wp_auto
      wp_method_call; wp_call
      wp_auto
      wp_apply h_ValidationErrors_WithLazyPrefix e2 [] f $$ [He2] as ⟨%es', Hes, %hl⟩
      · iframe He2; ileft; ipureintro; rfl
      have he : es' = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
      subst he
      iapply HΦ
      iframe
      iexists sp'
      isplitl; rotate_left
      · ipureintro; exact Hsp'
      unfold cwOwn cwCore ownCmp ownPath
      rw [hC]
      iexists ps'
      iframe
      iframe #
      ipureintro; exact Hwf'
    · rw [hlf] at hres
      simp only [↓reduceIte] at hres
      wp_auto
      wp_method_call; wp_call
      wp_auto
      wp_apply h_ValidationErrors_WithLazyPrefix e2 [] f $$ [He2] as ⟨%es', Hes, %hl⟩
      · iframe He2; ileft; ipureintro; rfl
      have he : es' = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
      subst he
      iapply HΦ
      iframe
      iexists sp'
      isplitl; rotate_left
      · ipureintro; exact Hsp'
      unfold cwOwn cwCore
      rw [hres]
      iexists ps'
      iframe
      iframe #
      ipureintro; exact Hwf'

  · ihave ⟨Hr, %Hrp⟩ := isValO_some $$ Hr
    obtain ⟨pr, Hpr⟩ := Hrp
    rcases l with _ | x
    · rw [Hln.2 rfl, Hpr]
      wp_auto
      ihave Hown : cwOwn w sc S st c C sp $$ [Hw Hp Hsp Ha Hc]
      · unfold cwOwn cwCore
        rw [Hln.2 rfl, Hpr]
        iexists ps
        iframe
        iframe #
        ipureintro; exact Hwf
      wp_apply h_handleAtom atm At tr (go.GoType.PointerType typed.compareWalker.ty) #w
        iprop(cwOwn w sc S st c C sp ∗ isValO GoInterface.nil dql none ∗ isValO (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #pr) dqr (some y))
        (fun errs => iprop(noErrs errs ∗ isValO GoInterface.nil dql none ∗ isValO (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #pr) dqr (some y) ∗
          (∃ sp' : Loc, cwOwn w sc S (CWSt.mk GoInterface.nil (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #pr) st.t st.path (leafAt S st.t none (some y)) st.alloc) c
            (C.union (cmpBelow S st.t st.path none (some y))) sp' ∗ ⌜sp ≠ null → sp' = sp⌝)))
        $$ [Hown Hl Hr] as %errs' HQ
      · iframe #; iframe

      icases HQ with ⟨Hes, Hl, Hr, %sp', Hown, %Hsp'⟩
      simp only [noErrs, ownErrs]
      icases Hes with ⟨Hes, Hcap⟩
      wp_apply (wp_slice_append (V := typed.ValidationError) slice.nil [] errs' [] (DFrac.own 1))
        $$ [Hes] as %e2 ⟨He2, Hcap2, -⟩
      · iframe
        isplitl
        · iapply ownSlice_nil
        · iapply ownSliceCap_nil
      simp only [List.append_nil]
      iunfold cwOwn at Hown
      icases Hown with ⟨%ps', Hcore, Hp, Hsp, Ha, Hc⟩
      iunfold cwCore at Hcore
      icases Hcore with ⟨%tr', Hw, #Htr', #Hsc', %Hwf'⟩
      have hres := cmpO_below_resolved S st.t st.path none (some y) hfind
      wp_auto
      iclear IH
      simp only
      cases hlf : leafAt S st.t none (some y)
      · rw [hlf] at hres
        have hC := LawB.cmp_node_added C (cmpBelow S st.t st.path none (some y)) st.path (some y)
        simp only [Bool.false_eq_true, ↓reduceIte] at hres
        rw [← hres] at hC
        unfold ownCmp; icases Hc with ⟨%rm, %md, %ad, Hcs, Hrm, Hmd, Had⟩
        unfold ownPath; icases Hp with ⟨Hpf, Hpcap⟩
        wp_auto
        have hcard : (C.union (cmpBelow S st.t st.path none (some y))).added.CardLt (2 ^ 63 - 1) := by
          have := Hpre.2.2.2.2.2.2
          rw [hC] at this
          exact LawB.cardLt_union_left _ _ _ this
        wp_apply h_Set_Insert ad _ ps' (DFrac.own 1) st.path $$ [Had Hpf] as ⟨Had, Hpf⟩
        · iframe; ipureintro; exact hcard
        wp_auto
        wp_method_call; wp_call
        wp_auto
        wp_apply h_ValidationErrors_WithLazyPrefix e2 [] f $$ [He2] as ⟨%es', Hes, %hl⟩
        · iframe He2; ileft; ipureintro; rfl
        have he : es' = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
        subst he
        iapply HΦ
        iframe
        iexists sp'
        isplitl; rotate_left
        · ipureintro; exact Hsp'
        unfold cwOwn cwCore ownCmp ownPath
        rw [hC]
        iexists ps'
        iframe
        iframe #
        ipureintro; exact Hwf'
      · rw [hlf] at hres
        simp only [↓reduceIte] at hres
        wp_auto
        wp_method_call; wp_call
        wp_auto
        wp_apply h_ValidationErrors_WithLazyPrefix e2 [] f $$ [He2] as ⟨%es', Hes, %hl⟩
        · iframe He2; ileft; ipureintro; rfl
        have he : es' = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
        subst he
        iapply HΦ
        iframe
        iexists sp'
        isplitl; rotate_left
        · ipureintro; exact Hsp'
        unfold cwOwn cwCore
        rw [hres]
        iexists ps'
        iframe
        iframe #
        ipureintro; exact Hwf'

    · ihave ⟨Hl, %Hlp⟩ := isValO_some $$ Hl
      obtain ⟨pl, Hpl⟩ := Hlp
      rw [Hpl, Hpr]
      wp_auto
      wp_apply h_Atom_Equals alhs_ptr arhs_ptr (DFrac.own 1) (DFrac.own 1) atm atm (some At) (some At)
        $$ [alhs arhs] as %b ⟨alhs, arhs, %Hb⟩
      · iframe #; iframe
      obtain rfl : b = true := Hb.2 rfl
      wp_auto
      ihave Hown : cwOwn w sc S st c C sp $$ [Hw Hp Hsp Ha Hc]
      · unfold cwOwn cwCore
        rw [Hpl, Hpr]
        iexists ps
        iframe
        iframe #
        ipureintro; exact Hwf
      wp_apply h_handleAtom atm At tr (go.GoType.PointerType typed.compareWalker.ty) #w
        iprop(cwOwn w sc S st c C sp ∗ isValO (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #pl) dql (some x) ∗ isValO (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #pr) dqr (some y))
        (fun errs => iprop(noErrs errs ∗ isValO (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #pl) dql (some x) ∗ isValO (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #pr) dqr (some y) ∗
          (∃ sp' : Loc, cwOwn w sc S (CWSt.mk (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #pl) (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #pr) st.t st.path (leafAt S st.t (some x) (some y)) st.alloc) c
            (C.union (cmpBelow S st.t st.path (some x) (some y))) sp' ∗ ⌜sp ≠ null → sp' = sp⌝)))
        $$ [Hown Hl Hr] as %errs' HQ
      · iframe #; iframe

      icases HQ with ⟨Hes, Hl, Hr, %sp', Hown, %Hsp'⟩
      simp only [noErrs, ownErrs]
      icases Hes with ⟨Hes, Hcap⟩
      wp_apply (wp_slice_append (V := typed.ValidationError) slice.nil [] errs' [] (DFrac.own 1))
        $$ [Hes] as %e2 ⟨He2, Hcap2, -⟩
      · iframe
        isplitl
        · iapply ownSlice_nil
        · iapply ownSliceCap_nil
      simp only [List.append_nil]
      iunfold cwOwn at Hown
      icases Hown with ⟨%ps', Hcore, Hp, Hsp, Ha, Hc⟩
      iunfold cwCore at Hcore
      icases Hcore with ⟨%tr', Hw, #Htr', #Hsc', %Hwf'⟩
      have hres := cmpO_below_resolved S st.t st.path (some x) (some y) hfind
      wp_auto
      iclear IH
      simp only
      have hC : C.union (cmpO S st.t st.path (some x) (some y)) = C.union (cmpBelow S st.t st.path (some x) (some y)) := by
        rw [hres]
        split
        · rfl
        · exact LawB.cmp_node_none C _ st.path x y
      generalize leafAt S st.t (some x) (some y) = b
      cases b <;> wp_auto
      all_goals
        wp_method_call; wp_call
        wp_auto
        wp_apply h_ValidationErrors_WithLazyPrefix e2 [] f $$ [He2] as ⟨%es', Hes, %hl⟩
        · iframe He2; ileft; ipureintro; rfl
        have he : es' = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
        subst he
        iapply HΦ
        iframe
        iexists sp'
        isplitl; rotate_left
        · ipureintro; exact Hsp'
        unfold cwOwn cwCore
        rw [hC]
        iexists ps'
        iframe
        iframe #
        ipureintro; exact Hwf'


end proof

end smd
end EtcdGrove
end Perennial
