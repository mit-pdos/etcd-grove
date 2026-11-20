/-
`typed.mergingWalker.merge`: a member of the recursion cluster `typed.mergingWalkerRec` (`mergingWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `mergingWalker__mergeBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__mergeBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Atom__Equals
public import Spec.sigs_k8s_io.structured_merge_diff.v7.schema.Schema__Resolve
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.ValidationErrors__WithLazyPrefix
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.deduceAtom
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.handleAtom
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBRecon
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__doScalar

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

instance atomHandlerOk_pers (A : Atom) (a : schema.Atom) (T : go.GoType) (hv : val) (Pre : IProp GF)
    (Q : GoSlice → IProp GF) : Persistent (atomHandlerOk A a T hv Pre Q) := by
  cases A <;> unfold atomHandlerOk <;> infer_instance

set_option synthInstance.maxHeartbeats 200000 in
set_option synthInstance.maxSize 4096 in
theorem typed.mergingWalker.merge.wp_proofBody
    (h_Atom_Equals : schema.Atom.Equals.spec (GF := GF))
    (h_Schema_Resolve : schema.Schema.Resolve.spec (GF := GF))
    (h_ValidationErrors_WithLazyPrefix : typed.ValidationErrors.WithLazyPrefix.spec (GF := GF))
    (h_deduceAtom : typed.deduceAtom.spec (GF := GF))
    (h_handleAtom : typed.handleAtom.spec (GF := GF))
    (h_mergingWalker_doScalar : typed.mergingWalker.doScalar.spec (GF := GF)) :
    typed.mergingWalker.merge.specBody (GF := GF) := by
  unfold typed.mergingWalker.merge.specBody typed.mergingWalkerRec.specI
    typed.mergingWalker.merge.specI typed.mergingWalker.doList.specI
    typed.mergingWalker.doMap.specI typed.mergingWalker.mergeListItem.specI
    typed.mergingWalker.visitListItems.specI typed.mergingWalker.visitMapItem.specI
    typed.mergingWalker.visitMapItems.specI
  iintro #IH
  iintro %w %sc %S %st %dql %dqr %l %r %f %sp
  wp_start as ⟨Hown, Hl, Hr, %Hpre⟩
  iunfold mwOwn at Hown
  icases Hown with ⟨%ps, %a, Hcore, Hp, Hsp, Ha⟩
  iunfold mwCore at Hcore
  icases Hcore with ⟨%tr, %rule, %o, Hw, #Htr, #Hsc, %Hwf, #Hrule, #Ho⟩
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
  ihave #Hah : atomHandlerOk At atm (go.GoType.PointerType typed.mergingWalker.ty) #w
      iprop(mwOwn w sc S st sp ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r)
      (fun errs => iprop(noErrs errs ∗ isValO st.lhs dql l ∗ isValO st.rhs dqr r ∗
        (∃ sp' : Loc, mwOwn w sc S (MWSt.mk st.lhs st.rhs st.t st.path (mergeO S st.t l r) (leafAt S st.t l r)) sp' ∗ ⌜sp ≠ null → sp' = sp⌝))) $$ []
  · icases IH with ⟨#HdL, #HdM, -, -, -, -, -⟩
    cases At with
    | scalar sk =>
      simp only [atomHandlerOk]
      icases (isAtomOpt_scalar_law_holds atm sk).1 $$ Hat with ⟨#Hs, -⟩
      imodintro
      iintro %Φ2 ⟨Hown, Hl, Hr⟩ HΦ2
      wp_apply h_mergingWalker_doScalar w sc S (st) dql dqr l r atm.Scalar' sk $$ [Hown Hl Hr]
        as %errs ⟨Herrs, Hl, Hr, Hown⟩
      · iframe #; iframe; ipureintro
        exact ⟨hA, Hpre.1, Hpre.2.1, Hpre.2.2.1, Hpre.2.2.2.2⟩
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
  · rw [Hrn.2 rfl]
    wp_auto
    ihave Hown : mwOwn w sc S st sp $$ [Hw Hp Hsp Ha]
    · unfold mwOwn mwCore
      rw [Hrn.2 rfl]
      iexists ps, a
      iframe
      iframe #
      ipureintro; exact Hwf
    wp_apply h_handleAtom atm At tr (go.GoType.PointerType typed.mergingWalker.ty) #w
      iprop(mwOwn w sc S st sp ∗ isValO st.lhs dql l ∗ isValO GoInterface.nil dqr none)
      (fun errs => iprop(noErrs errs ∗ isValO st.lhs dql l ∗ isValO GoInterface.nil dqr none ∗
        (∃ sp' : Loc, mwOwn w sc S (MWSt.mk st.lhs GoInterface.nil st.t st.path (mergeO S st.t l none) (leafAt S st.t l none)) sp' ∗ ⌜sp ≠ null → sp' = sp⌝)))
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
    iunfold mwOwn at Hown
    icases Hown with ⟨%ps', %a', Hcore, Hp, Hsp, Ha⟩
    iunfold mwCore at Hcore
    icases Hcore with ⟨%tr', %rule', %o', Hw, #Htr', #Hsc', %Hwf', #Hrule', #Ho'⟩
    wp_auto
    wp_join at (if: _ then _ else _) with [Hw w]
    · generalize leafAt S st.t l none = b
      cases b <;> (wp_auto; try wp_join_done)
    simp only [List.append_nil]
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
    unfold mwOwn mwCore
    iexists ps', a'
    iframe
    iframe #
    ipureintro; exact Hwf'
  · ihave ⟨Hr, %Hrp⟩ := isValO_some $$ Hr
    obtain ⟨pr, Hpr⟩ := Hrp
    rcases l with _ | x
    · rw [Hln.2 rfl, Hpr]
      wp_auto
      ihave Hown : mwOwn w sc S st sp $$ [Hw Hp Hsp Ha]
      · unfold mwOwn mwCore
        rw [Hln.2 rfl, Hpr]
        iexists ps, a
        iframe
        iframe #
        ipureintro; exact Hwf
      wp_apply h_handleAtom atm At tr (go.GoType.PointerType typed.mergingWalker.ty) #w
        iprop(mwOwn w sc S st sp ∗ isValO GoInterface.nil dql none ∗ isValO (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #pr) dqr (some y))
        (fun errs => iprop(noErrs errs ∗ isValO GoInterface.nil dql none ∗ isValO (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #pr) dqr (some y) ∗
          (∃ sp' : Loc, mwOwn w sc S (MWSt.mk GoInterface.nil (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #pr) st.t st.path (mergeO S st.t none (some y)) (leafAt S st.t none (some y))) sp' ∗ ⌜sp ≠ null → sp' = sp⌝)))
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
      iunfold mwOwn at Hown
      icases Hown with ⟨%ps', %a', Hcore, Hp, Hsp, Ha⟩
      iunfold mwCore at Hcore
      icases Hcore with ⟨%tr', %rule', %o', Hw, #Htr', #Hsc', %Hwf', #Hrule', #Ho'⟩
      wp_auto
      wp_join at (if: _ then _ else _) with [Hw w]
      · generalize leafAt S st.t none (some y) = b
        cases b <;> (wp_auto; try wp_join_done)
      simp only [List.append_nil]
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
      unfold mwOwn mwCore
      iexists ps', a'
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
      ihave Hown : mwOwn w sc S st sp $$ [Hw Hp Hsp Ha]
      · unfold mwOwn mwCore
        rw [Hpl, Hpr]
        iexists ps, a
        iframe
        iframe #
        ipureintro; exact Hwf
      wp_apply h_handleAtom atm At tr (go.GoType.PointerType typed.mergingWalker.ty) #w
        iprop(mwOwn w sc S st sp ∗ isValO (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #pl) dql (some x) ∗ isValO (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #pr) dqr (some y))
        (fun errs => iprop(noErrs errs ∗ isValO (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #pl) dql (some x) ∗ isValO (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #pr) dqr (some y) ∗
          (∃ sp' : Loc, mwOwn w sc S (MWSt.mk (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #pl) (interface.mkOk (go.GoType.PointerType value.valueUnstructured.ty) #pr) st.t st.path (mergeO S st.t (some x) (some y)) (leafAt S st.t (some x) (some y))) sp' ∗ ⌜sp ≠ null → sp' = sp⌝)))
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
      iunfold mwOwn at Hown
      icases Hown with ⟨%ps', %a', Hcore, Hp, Hsp, Ha⟩
      iunfold mwCore at Hcore
      icases Hcore with ⟨%tr', %rule', %o', Hw, #Htr', #Hsc', %Hwf', #Hrule', #Ho'⟩
      wp_auto
      wp_join at (if: _ then _ else _) with [Hw w]
      · generalize leafAt S st.t (some x) (some y) = b
        cases b <;> (wp_auto; try wp_join_done)
      simp only [List.append_nil]
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
      unfold mwOwn mwCore
      iexists ps', a'
      iframe
      iframe #
      ipureintro; exact Hwf'


end proof

end smd
end EtcdGrove
end Perennial
