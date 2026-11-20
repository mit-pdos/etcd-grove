/-
`typed.mergingWalker.doList`: a member of the recursion cluster `typed.mergingWalkerRec` (`mergingWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `mergingWalker__doListBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__doListBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.listUnstructured__Length_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__derefList
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mergingWalker__doLeaf
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

set_option synthInstance.maxHeartbeats 200000 in
set_option synthInstance.maxSize 4096 in
theorem typed.mergingWalker.doList.wp_proofBody
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_listUnstructured_Length : value.listUnstructured.Length.spec (GF := GF))
    (h_listUnstructured_Length_ptr : value.listUnstructured.Length_ptr.spec (GF := GF))
    (h_mergingWalker_derefList : typed.mergingWalker.derefList.spec (GF := GF))
    (h_mergingWalker_doLeaf : typed.mergingWalker.doLeaf.spec (GF := GF)) :
    typed.mergingWalker.doList.specBody (GF := GF) := by
  unfold typed.mergingWalker.doList.specBody typed.mergingWalkerRec.specI
    typed.mergingWalker.merge.specI typed.mergingWalker.doList.specI
    typed.mergingWalker.doMap.specI typed.mergingWalker.mergeListItem.specI
    typed.mergingWalker.visitListItems.specI typed.mergingWalker.visitMapItem.specI
    typed.mergingWalker.visitMapItems.specI
  iintro #IH
  iintro %w %sc %S %st %dql %dqr %l %r %tp %e %rel %ks %sp
  wp_start as ⟨Hown, Hl, Hr, #Hlr, %Hpre⟩
  obtain ⟨Hfind, Hsome, Hcl, Hcr, Hout, Hleaf⟩ := Hpre
  icases IH with ⟨-, -, -, -, #HvL, -⟩
  have hside : ∀ o, confO S st.t o → o = none ∨ o = some .null ∨ (listOfO o).isSome := by
    intro o ho
    rcases o with _ | x
    · left; rfl
    · right
      simp only [confO] at ho
      unfold conforms at ho
      cases x <;> simp_all [conformsB, listOfO]
  iunfold mwOwn at Hown
  icases Hown with ⟨%ps, Hcore, Hp, Hsp, Ha⟩
  iunfold mwCore at Hcore
  icases Hcore with ⟨%tr, %rule, %o, Hw, #Htr, #Hsc, %Hwf, #Hrule, #Ho⟩
  icases isListRep_elim_law_holds tp e rel ks $$ Hlr with ⟨%lv, %ksl, #Hlv, %Hlv', -, #Het⟩
  ihave ⟨Hlv2, %Hnn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hlv
  iStructNamed Hlv2
  wp_auto
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  ihave ⟨Ha, %ia, %Hai, #Hfree⟩ := isAlloc_Free h_heapAllocator_Free h_freelistAllocator_Free st.alloc $$ [Ha]
  · iframe Ha; iPkgInit
  rw [Hai]
  wp_apply h_mergingWalker_derefList w _ (DFrac.own 1) _ st.lhs dql l $$ [Hw Hl] as %ll %e1 ⟨Hw, Hl, Hll, -⟩
  · iframe; ipureintro; exact hside l Hcl
  try wp_auto
  have hli : ∀ o, listItems o = (listOfO o).getD [] := by
    intro o; rcases o with _ | ⟨_ | _ | _ | _ | _ | _⟩ <;> rfl
  have hleafv : leafAt S st.t l r = (decide (rel = .atomic) ||
      (((listOfO l).getD []).isEmpty && ((listOfO r).getD []).isEmpty)) := by
    simp only [leafAt, Hfind, hli]
  have hgn : decide (ElemRel.goName rel = go!"atomic") = decide (rel = ElemRel.atomic) := by
    simp [LawB.goName_atomic]
  rw [Hlv'.1]
  have hcm : ∀ o, confO S st.t o → confO S st.t ((listOfO o).map UVal.list) := by
    intro o ho; rcases o with _ | ⟨_ | _ | _ | _ | vs | _⟩ <;> simp_all [listOfO, confO]
  rcases hlf : leafAt S st.t l r
  all_goals
    rcases hlo : listOfO l with _ | vsl
    case' none =>
      iunfold isListO at Hll
      icases Hll with %Hll
      subst Hll
      wp_auto
    case' some =>
      iunfold isListO at Hll
      ihave #Hllv := isListV_persistent_law_holds ll vsl $$ Hll
      ihave ⟨%il, %Hil, #HlenL⟩ := isListV_Length h_listUnstructured_Length h_listUnstructured_Length_ptr ll vsl $$ [Hllv]
      · iframe #; iPkgInit
      subst Hil
      wp_auto
  all_goals
    wp_apply h_mergingWalker_derefList w _ (DFrac.own 1) _ st.rhs dqr r $$ [Hw Hr] as %rl %e2 ⟨Hw, Hr, Hrl, -⟩
    · iframe; ipureintro; exact hside r Hcr
    try wp_auto
  all_goals
    rcases hro : listOfO r with _ | vsr
    case' none =>
      iunfold isListO at Hrl
      icases Hrl with %Hrl
      subst Hrl
      wp_auto
    case' some =>
      iunfold isListO at Hrl
      ihave #Hrlv := isListV_persistent_law_holds rl vsr $$ Hrl
      ihave ⟨%ir, %Hir, #HlenR⟩ := isListV_Length h_listUnstructured_Length h_listUnstructured_Length_ptr rl vsr $$ [Hrlv]
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
    try (rw [show decide (nl = W64 0) = decide (vsl = []) from decide_eq_decide.2 (LawB.w64_len_zero nl vsl Hnl)])
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
    try (rw [show decide (nr = W64 0) = decide (vsr = []) from decide_eq_decide.2 (LawB.w64_len_zero nr vsr Hnr)])
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
    | (guard_hyp hlf : leafAt S st.t l r = false
       have hleaf : leafAt S st.t l r = false := hlf
       try wp_auto
       obtain ⟨hra, -⟩ := LawB.list_wf S Hwf st.t e rel ks Hfind
         (by intro h; subst h; simp [leafAt, Hfind] at hleaf)
       subst hra
       ihave Hown : mwOwn w sc S st sp $$ [Hw Hp Hsp Ha]
       · unfold mwOwn mwCore
         try rw [Hai]
         iexists ps
         iframe
         iframe #
         ipureintro; exact Hwf
       wp_apply HvL $$ %w %sc %S %st %tp %e %ks %_ %_ %(listOfO l) %(listOfO r) %sp [Hown]
         as %errs ⟨Herrs, %sp', Hown, %Hsp'⟩
       · iframe; iframe #
         rw [hlo, hro]
         simp only [isListO]
         iframe #
         ipureintro
         refine ⟨Hfind, Hout, Hleaf, ?_, ?_⟩
         · have := hcm l Hcl; rw [hlo] at this; exact this
         · have := hcm r Hcr; rw [hro] at this; exact this
       iunfold mwOwn at Hown
       icases Hown with ⟨%ps', Hcore, Hp, Hsp, Ha⟩
       simp only
       try rw [Hai]
       try wp_auto
       try (ihave ⟨-, HfR⟩ := (freeable_view_law_holds).2.1 _ _ $$ Hrlv)
       try (wp_apply Hfree $$ %_ [Ha HfR] as Ha <;> try (isplitl [Ha]; iexact Ha; iexact HfR))
       try wp_auto
       try (ihave ⟨-, HfL⟩ := (freeable_view_law_holds).2.1 _ _ $$ Hllv)
       try (wp_apply Hfree $$ %_ [Ha HfL] as Ha <;> try (isplitl [Ha]; iexact Ha; iexact HfL))
       try wp_auto
       iapply HΦ
       iframe
       iexists sp'
       isplitl; rotate_left
       · ipureintro; exact Hsp'
       rw [mergeO_list_law_holds S st.t e .associative ks l r Hfind hleaf, hli l, hli r, hlo, hro]
       simp only [Hleaf]
       unfold mwOwn
       iexists ps'
       try rw [Hai]
       iframe)
    | (guard_hyp hlf : leafAt S st.t l r = true
       have hleaf : leafAt S st.t l r = true := hlf
       ihave Hown : mwOwn w sc S st sp $$ [Hw Hp Hsp Ha]
       · unfold mwOwn mwCore
         try rw [Hai]
         iexists ps
         iframe
         iframe #
         ipureintro; exact Hwf
       wp_apply h_mergingWalker_doLeaf w sc S st dql dqr l r sp $$ [Hown Hl Hr] as ⟨Hl, Hr, Hown⟩
       · iframe; ipureintro; exact Hsome
       simp only [Hleaf, Bool.false_eq_true, ↓reduceIte]
       iunfold mwOwn at Hown
       icases Hown with ⟨%ps', Hcore, Hp, Hsp, Ha⟩
       simp only
       try rw [Hai]
       try wp_auto
       try (ihave ⟨-, HfR⟩ := (freeable_view_law_holds).2.1 _ _ $$ Hrlv)
       try (wp_apply Hfree $$ %_ [Ha HfR] as Ha <;> try (isplitl [Ha]; iexact Ha; iexact HfR))
       try wp_auto
       try (ihave ⟨-, HfL⟩ := (freeable_view_law_holds).2.1 _ _ $$ Hllv)
       try (wp_apply Hfree $$ %_ [Ha HfL] as Ha <;> try (isplitl [Ha]; iexact Ha; iexact HfL))
       try wp_auto
       iapply HΦ
       isplitr
       · iapply noErrs_nil
       iframe
       iexists sp
       isplitl; rotate_left
       · ipureintro; intro _; rfl
       rw [mergeO_leaf_law_holds S st.t l r hleaf Hsome]
       unfold mwOwn
       iexists ps'
       try rw [Hai]
       iframe)

end proof

end smd
end EtcdGrove
end Perennial
