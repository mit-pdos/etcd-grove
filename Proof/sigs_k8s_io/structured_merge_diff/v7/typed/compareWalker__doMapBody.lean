/-
`typed.compareWalker.doMap`: a member of the recursion cluster `typed.compareWalkerRec` (`compareWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `compareWalker__doMapBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__doMapBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.mapUnstructuredString__Empty
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__derefMap
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.compareWalker__doLeaf
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBRecon
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBList
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsDispatch
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false

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

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
set_option synthInstance.maxSize 4096 in
theorem typed.compareWalker.doMap.wp_proofBody
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_mapUnstructuredString_Empty : value.mapUnstructuredString.Empty.spec (GF := GF))
    (h_compareWalker_derefMap : typed.compareWalker.derefMap.spec (GF := GF))
    (h_compareWalker_doLeaf : typed.compareWalker.doLeaf.spec (GF := GF)) :
    typed.compareWalker.doMap.specBody (GF := GF) := by
  unfold typed.compareWalker.doMap.specBody typed.compareWalkerRec.specI
    typed.compareWalker.compare.specI typed.compareWalker.compareListItem.specI
    typed.compareWalker.doList.specI typed.compareWalker.doMap.specI
    typed.compareWalker.visitListItems.specI typed.compareWalker.visitMapItem.specI
    typed.compareWalker.visitMapItems.specI
  iintro #IH
  iintro %w %sc %S %st %c %C %dql %dqr %l %r %tp %fs %em %rel %sp
  wp_start as ⟨Hown, Hl, Hr, #Hmr, %Hpre⟩
  obtain ⟨Hfind, Hsome, Hcl, Hcr, Hleaf, Hrm, Hmd, Had⟩ := Hpre
  icases IH with ⟨-, -, -, -, -, -, #HvM⟩
  have hres := cmpO_below_resolved S st.t st.path l r (by rw [Hfind]; rfl)
  have hside : ∀ o, confO S st.t o → o = none ∨ o = some .null ∨ (mapOfO o).isSome := by
    intro o ho
    rcases o with _ | x
    · left; rfl
    · right
      simp only [confO] at ho
      unfold conforms at ho
      cases x <;> simp_all [conformsB, mapOfO]
  iunfold cwOwn at Hown
  icases Hown with ⟨%ps, Hcore, Hp, Hsp, Ha, Hc⟩
  iunfold cwCore at Hcore
  icases Hcore with ⟨%tr, Hw, #Htr, #Hsc, %Hwf⟩
  icases isMapRep_elim_law_holds tp fs em rel $$ Hmr with
    ⟨%fsl, %sfs, %etv, -, -, -, -, -, #Het, #Hetv, #Hrel⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  ihave ⟨Ha, %ia, %Hai, #Hfree⟩ := isAlloc_Free h_heapAllocator_Free h_freelistAllocator_Free st.alloc $$ [Ha]
  · iframe Ha; iPkgInit
  rw [Hai]
  wp_apply h_compareWalker_derefMap w _ (DFrac.own 1) _ st.lhs dql l $$ [Hw Hl] as %ll %e1 ⟨Hw, Hl, Hll, -⟩
  · iframe; ipureintro; exact hside l Hcl
  try wp_auto
  have hli : ∀ o, mapItems o = (mapOfO o).getD [] := by
    intro o; rcases o with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl
  have hleafv : leafAt S st.t l r = (decide (rel = .atomic) ||
      (((mapOfO l).getD []).isEmpty && ((mapOfO r).getD []).isEmpty)) := by
    simp only [leafAt, Hfind, hli]
  have hgn : decide (ElemRel.goName rel = go!"atomic") = decide (rel = ElemRel.atomic) := by
    simp [LawB.goName_atomic]
  have hcm : ∀ o, confO S st.t o → confO S st.t ((mapOfO o).map UVal.map) := by
    intro o ho; rcases o with _ | ⟨_ | _ | _ | _ | _ | kvs⟩ <;> simp_all [mapOfO, confO]
  rcases hlf : leafAt S st.t l r
  all_goals
    rcases hlo : mapOfO l with _ | vsl
    case' none =>
      iunfold isMapO at Hll
      icases Hll with %Hll
      subst Hll
      wp_auto
    case' some =>
      iunfold isMapO at Hll
      ihave #Hllv := isMapV_persistent_law_holds ll vsl $$ Hll
      ihave ⟨%il, %Hil, #HlenL⟩ := isMapV_Empty h_mapUnstructuredString_Empty ll vsl $$ [Hllv]
      · iframe #; iPkgInit
      subst Hil
      wp_auto
  all_goals
    wp_apply h_compareWalker_derefMap w _ (DFrac.own 1) _ st.rhs dqr r $$ [Hw Hr] as %rl %e2 ⟨Hw, Hr, Hrl, -⟩
    · iframe; ipureintro; exact hside r Hcr
    try wp_auto
  all_goals
    rcases hro : mapOfO r with _ | vsr
    case' none =>
      iunfold isMapO at Hrl
      icases Hrl with %Hrl
      subst Hrl
      wp_auto
    case' some =>
      iunfold isMapO at Hrl
      ihave #Hrlv := isMapV_persistent_law_holds rl vsr $$ Hrl
      ihave ⟨%ir, %Hir, #HlenR⟩ := isMapV_Empty h_mapUnstructuredString_Empty rl vsr $$ [Hrlv]
      · iframe #; iPkgInit
      subst Hir
      wp_auto
  all_goals
    try (wp_apply HlenL as %nl %Hnl)
  all_goals
    try iexact Hllv
  all_goals
    try wp_auto
  all_goals
    try (obtain rfl : nl = decide (vsl = []) := by cases nl <;> simp_all)
  all_goals
    try wp_if_destruct
  all_goals
    try (have HvlE := Hif; clear Hif)
  all_goals
    try (wp_apply HlenR as %nr %Hnr)
  all_goals
    try iexact Hrlv
  all_goals
    try wp_auto
  all_goals
    try (obtain rfl : nr = decide (vsr = []) := by cases nr <;> simp_all)
  all_goals
    try wp_if_destruct
  all_goals
    try (have HvrE := Hif; clear Hif)
  all_goals
    try wp_auto
  all_goals
    try (rw [hgn])
  all_goals
    try wp_if_destruct
  all_goals
    try (have HrelE := Hif; clear Hif)
  all_goals
    first
    | (exfalso
       rw [hlo, hro, hlf] at hleafv
       try rw [Hlv'.1] at HvlE
       try rw [Hlv'.1] at HvrE
       try rw [Hlv'.1] at HrelE
       try rw [LawB.goName_atomic] at HvlE
       try rw [LawB.goName_atomic] at HvrE
       try rw [LawB.goName_atomic] at HrelE
       revert hleafv
       try revert HrelE
       try revert HvrE
       try revert HvlE
       simp +contextual
       done)
    | (guard_hyp hlf : leafAt S st.t l r = true
       have hleaf : leafAt S st.t l r = true := hlf
       ihave Hown : cwOwn w sc S st c C sp $$ [Hw Hp Hsp Ha Hc]
       · unfold cwOwn cwCore
         try rw [Hai]
         iexists ps
         iframe
         iframe #
         ipureintro; exact Hwf
       have hcb : cmpBelow S st.t st.path l r = leafC st.path l r := by
         unfold cmpBelow; rw [hleaf]; rfl
       have hco : cmpO S st.t st.path l r = leafC st.path l r := by rw [hres, hleaf, hcb]; rfl
       rw [hco] at Hrm Hmd Had
       wp_apply h_compareWalker_doLeaf w sc S st c C dql dqr l r sp $$ [Hown Hl Hr] as ⟨Hl, Hr, Hown⟩
       · iframe; ipureintro; exact ⟨Hsome, Hrm, Hmd, Had⟩
       simp only [Hleaf, Bool.false_eq_true, ↓reduceIte]
       iunfold cwOwn at Hown
       icases Hown with ⟨%ps', Hcore, Hp, Hsp, Ha, Hc⟩
       simp only
       try rw [Hai]
       try wp_auto
       try (ihave ⟨-, HfR⟩ := (freeable_view_law_holds).1 _ _ $$ Hrlv)
       try (wp_apply Hfree $$ %_ [Ha HfR] as Ha <;> try (isplitl [Ha]; iexact Ha; iexact HfR))
       try wp_auto
       try (ihave ⟨-, HfL⟩ := (freeable_view_law_holds).1 _ _ $$ Hllv)
       try (wp_apply Hfree $$ %_ [Ha HfL] as Ha <;> try (isplitl [Ha]; iexact Ha; iexact HfL))
       try wp_auto
       iapply HΦ
       isplitr
       · iapply noErrs_nil
       iframe
       iexists sp
       isplitl; rotate_left
       · ipureintro; intro _; rfl
       rw [hcb]
       unfold cwOwn
       iexists ps'
       try rw [Hai]
       iframe)
    | (guard_hyp hlf : leafAt S st.t l r = false
       have hleaf : leafAt S st.t l r = false := hlf
       try wp_auto
       ihave Hown : cwOwn w sc S st c C sp $$ [Hw Hp Hsp Ha Hc]
       · unfold cwOwn cwCore
         try rw [Hai]
         iexists ps
         iframe
         iframe #
         ipureintro; exact Hwf
       have hcb := LawB.cmpBelow_map S st.t fs em rel st.path l r Hfind hleaf
       have hco : cmpO S st.t st.path l r = (cmpBelow S st.t st.path l r).union (nodeC st.path l r) := by
         rw [hres, hleaf]; rfl
       rw [hco] at Hrm Hmd Had
       obtain ⟨Hrm', Hmd', Had'⟩ := LawB.cmp_cardLt_below _ _ _ _ Hrm Hmd Had
       rw [hcb, hli l, hli r] at Hrm' Hmd' Had'
       wp_apply HvM $$ %w %sc %S %st %c %C %tp %fs %em %rel %_ %_ %(mapOfO l) %(mapOfO r) %sp [Hown]
         as %errs ⟨Herrs, %sp', Hown, %Hsp'⟩
       · iframe; iframe #
         rw [hlo, hro]
         simp only [isMapO]
         iframe #
         ipureintro
         rw [hlo, hro] at Hrm' Hmd' Had'
         have h1 := hcm l Hcl
         have h2 := hcm r Hcr
         rw [hlo] at h1
         rw [hro] at h2
         refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | exact Hfind | exact Hleaf | exact h1 | exact h2 | exact Hrm' | exact Hmd' | exact Had'
       iunfold cwOwn at Hown
       icases Hown with ⟨%ps', Hcore, Hp, Hsp, Ha, Hc⟩
       try simp only
       try rw [Hai]
       try wp_auto
       simp only [noErrs, ownErrs]
       icases Herrs with ⟨Herrs, Hcap⟩
       wp_apply (wp_slice_append (V := typed.ValidationError) slice.nil [] errs [] (DFrac.own 1))
         $$ [Herrs] as %e2 ⟨He2, Hcap2, -⟩
       · iframe
         isplitl
         · iapply ownSlice_nil
         · iapply ownSliceCap_nil
       simp only [List.append_nil]
       try wp_auto
       try (ihave ⟨-, HfR⟩ := (freeable_view_law_holds).1 _ _ $$ Hrlv)
       try (wp_apply Hfree $$ %_ [Ha HfR] as Ha <;> try (isplitl [Ha]; iexact Ha; iexact HfR))
       try wp_auto
       try (ihave ⟨-, HfL⟩ := (freeable_view_law_holds).1 _ _ $$ Hllv)
       try (wp_apply Hfree $$ %_ [Ha HfL] as Ha <;> try (isplitl [Ha]; iexact Ha; iexact HfL))
       try wp_auto
       iapply HΦ
       iframe
       iexists sp'
       isplitl; rotate_left
       · ipureintro; exact Hsp'
       rw [hcb, hli l, hli r, hlo, hro, ← Hai, LawB.CWSt.with_inLeaf st false Hleaf]
       unfold cwOwn
       iexists ps'
       try rw [Hai]
       iframe)


end proof

end smd
end EtcdGrove
end Perennial
