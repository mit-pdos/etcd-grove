/-
`typed.toFieldSetWalker.doList`: a member of the recursion cluster `typed.toFieldSetWalkerRec` (`toFieldSetWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `toFieldSetWalker__doListBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__doListBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.listValue
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsAPure
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsB2
public import Proof.sigs_k8s_io.structured_merge_diff.v7.schema.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.value.LawProofsDispatch

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
theorem typed.toFieldSetWalker.doList.wp_proofBody
    (h_Set_Insert : fieldpath.Set.Insert.spec (GF := GF))
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_listValue : typed.listValue.spec (GF := GF)) :
    typed.toFieldSetWalker.doList.specBody (GF := GF) := by
  unfold typed.toFieldSetWalker.doList.specBody typed.toFieldSetWalkerRec.specI
    typed.toFieldSetWalker.toFieldSet.specI typed.toFieldSetWalker.doList.specI
    typed.toFieldSetWalker.doMap.specI typed.toFieldSetWalker.visitListItems.specI
    typed.toFieldSetWalker.visitMapItems.specI
  iintro #IH
  iintro %w %sc %S %st %s %F %dq %x %tp %e %rel %ks %sp
  wp_start as ⟨Hown, Hv, #Hl, %Hpre⟩
  obtain ⟨Hfind, Hc, Hcard⟩ := Hpre
  have Hx : x = .null ∨ (listOfO (some x)).isSome := by
    unfold conforms at Hc
    cases x <;> simp_all [conformsB, listOfO]
  iunfold twOwn at Hown
  icases Hown with ⟨%ps, Hcore, Hps, Hsp, Ha, Hs⟩
  iunfold twCore at Hcore
  icases Hcore with ⟨%tr, Hw, #Htr, #Hsc, %Hwf⟩
  icases isListRep_elim_law_holds tp e rel ks $$ Hl with ⟨%lv, %ksl, #Hlv, %Hlv', -, -⟩
  ihave ⟨Hlv2, %Hnn⟩ := typedPointsto_not_null_dup _ _ _ $$ Hlv
  iStructNamed Hlv2
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply h_listValue st.alloc st.value dq x $$ [Hv] as %l %err ⟨Hv, Hlo, %Herr⟩
  · iframe Hv; ipureintro; exact Hx
  rcases Hx with rfl | Hx
  · simp only [listOfO, isListO]
    icases Hlo with %Hlo
    subst Hlo
    wp_auto
    rw [Hlv'.1]
    by_cases hr : rel = .atomic
    · subst hr
      have hfa : fieldsAt S st.t st.path .null = ins st.path := by simp [fieldsAt, Hfind]
      rw [hfa] at Hcard ⊢
      simp only [ElemRel.goName, _root_.decide_true]
      wp_auto
      unfold ownPath
      icases Hps with ⟨Hpf, Hpc⟩
      wp_apply h_Set_Insert s F ps (DFrac.own 1) st.path $$ [Hs Hpf] as ⟨Hs, Hpf⟩
      · iframe; ipureintro; exact LawB.cardLt_union_left _ _ _ Hcard
      iapply HΦ
      iframe
      isplitr
      · iapply noErrs_nil
      iexists sp
      isplitl
      · unfold twOwn twCore ownPath
        iexists ps
        iframe
        iframe #
        ipureintro; exact Hwf
      ipureintro; intro; rfl
    · have hg : decide (rel.goName = go!"atomic") = false := by
        cases rel <;> first | exact absurd rfl hr | decide
      have hfa : fieldsAt S st.t st.path .null = empty := by
        cases rel <;> first | exact absurd rfl hr | simp [fieldsAt, Hfind]
      have hue : F.union empty = F := LawB.fset_union_empty F
      rw [hfa, hue]
      rw [hg]
      wp_auto
      iapply HΦ
      iframe
      isplitr
      · iapply noErrs_nil
      iexists sp
      isplitl
      · unfold twOwn twCore ownPath
        iexists ps
        iframe
        iframe #
        ipureintro; exact Hwf
      ipureintro; intro; rfl
  obtain ⟨vs, rfl⟩ : ∃ vs, x = .list vs := by
    cases x <;> simp [listOfO] at Hx ⊢
  simp only [listOfO, isListO]
  ihave #Hll := isListV_persistent_law_holds l vs $$ Hlo
  ihave %Hlc := isListV_concrete_law_holds l vs $$ Hll
  rcases Hlc with ⟨sl, rfl⟩ | ⟨pl, rfl⟩
  all_goals
    ihave ⟨Ha, %i, %Hai, #Hfree⟩ := isAlloc_Free h_heapAllocator_Free h_freelistAllocator_Free st.alloc $$ [Ha]
    · iframe Ha; iPkgInit
    rw [Hai]
    wp_auto
    rw [Hlv'.1]
    by_cases hr : rel = .atomic
    · subst hr
      have hfa : fieldsAt S st.t st.path (.list vs) = ins st.path := by simp [fieldsAt, Hfind]
      rw [hfa] at Hcard ⊢
      simp only [ElemRel.goName, _root_.decide_true]
      wp_auto
      unfold ownPath
      icases Hps with ⟨Hpf, Hpc⟩
      wp_apply h_Set_Insert s F ps (DFrac.own 1) st.path $$ [Hs Hpf] as ⟨Hs, Hpf⟩
      · iframe; ipureintro; exact LawB.cardLt_union_left _ _ _ Hcard
      wp_apply Hfree $$ %_ [Ha] as Ha
      · iframe; ihave ⟨-, Hf⟩ := (freeable_view_law_holds).2.1 _ vs $$ Hll; iexact Hf
      iapply HΦ
      iframe
      isplitr
      · iapply noErrs_nil
      iexists sp
      isplitl
      · unfold twOwn twCore ownPath
        iexists ps
        rw [Hai]
        iframe
        iframe #
        ipureintro; exact Hwf
      ipureintro; intro; rfl
    · obtain ⟨hrel, -⟩ := LawB.list_wf S Hwf st.t e rel ks Hfind hr
      subst hrel
      have hfa : fieldsAt S st.t st.path (.list vs) = fieldsL S e ks st.path vs := by
        simp [fieldsAt, Hfind]
      rw [hfa] at Hcard ⊢
      simp only [ElemRel.goName]
      wp_auto
      icases IH with ⟨-, -, -, #HvL, -⟩
      wp_apply HvL $$ %w %sc %S %st %s %F %tp %e %ks %_ %vs %sp [Hw Hps Hsp Ha Hs] as %errs ⟨Herrs, Hown⟩
      · iframe #
        isplitl [Hw Hps Hsp Ha Hs]
        · unfold twOwn twCore
          iexists ps
          rw [Hai]
          iframe
          iframe #
          ipureintro; exact Hwf
        ipureintro; exact ⟨Hfind, Hc, Hcard⟩
      iunfold twOwn at Hown
      icases Hown with ⟨%sp', ⟨%ps', Hcore', Hps', Hsp', Ha', Hs'⟩, %Hsp'⟩
      rw [Hai]
      wp_apply Hfree $$ %_ [Ha'] as Ha'
      · iframe; ihave ⟨-, Hf⟩ := (freeable_view_law_holds).2.1 _ vs $$ Hll; iexact Hf
      iapply HΦ
      iframe
      iexists sp'
      isplitl
      · unfold twOwn
        iexists ps'
        rw [Hai]
        iframe
      ipureintro; exact Hsp'
