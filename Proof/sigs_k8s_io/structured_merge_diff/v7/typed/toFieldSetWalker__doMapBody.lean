/-
`typed.toFieldSetWalker.doMap`: a member of the recursion cluster `typed.toFieldSetWalkerRec` (`toFieldSetWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `toFieldSetWalker__doMapBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.toFieldSetWalker__doMapBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Set__Insert
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mapValue
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

theorem typed.toFieldSetWalker.doMap.wp_proofBody
    (h_Set_Insert : fieldpath.Set.Insert.spec (GF := GF))
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_mapValue : typed.mapValue.spec (GF := GF)) :
    typed.toFieldSetWalker.doMap.specBody (GF := GF) := by
  unfold typed.toFieldSetWalker.doMap.specBody typed.toFieldSetWalkerRec.specI
    typed.toFieldSetWalker.toFieldSet.specI typed.toFieldSetWalker.doList.specI
    typed.toFieldSetWalker.doMap.specI typed.toFieldSetWalker.visitListItems.specI
    typed.toFieldSetWalker.visitMapItems.specI
  iintro #IH
  iintro %w %sc %S %st %s %F %dq %x %tp %fs %e %rel
  wp_start as ⟨Hown, Hv, #Hm, %Hpre⟩
  obtain ⟨Hfind, Hc, Hcard⟩ := Hpre
  have Hx : some x = some .null ∨ (mapOfO (some x)).isSome := by
    unfold conforms at Hc
    cases x <;> simp_all [conformsB, mapOfO]
  iunfold twOwn at Hown
  icases Hown with ⟨%ps, %sp, Hcore, Hps, Hsp, Ha, Hs⟩
  iunfold twCore at Hcore
  icases Hcore with ⟨%tr, Hw, #Htr, #Hsc, %Hwf⟩
  icases isMapRep_elim_law_holds tp fs e rel $$ Hm with ⟨%fsl, %sfs, %etv, -, -, -, -, -, -, -, #Hrel⟩
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply h_mapValue st.alloc st.value dq (some x) $$ [Hv] as %m %err ⟨Hv, Hmo, %Herr⟩
  · simp only [isValO]; iframe Hv; ipureintro; exact Hx
  simp only [isValO]
  rcases Hx with Hx | Hx
  · cases Hx
    simp only [mapOfO, isMapO]
    icases Hmo with %Hmo
    subst Hmo
    wp_auto
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
      unfold twOwn twCore ownPath
      iexists ps, sp
      iframe
      iframe #
      ipureintro; exact Hwf
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
      unfold twOwn twCore ownPath
      iexists ps, sp
      iframe
      iframe #
      ipureintro; exact Hwf
  obtain ⟨kvs, rfl⟩ : ∃ kvs, x = .map kvs := by
    cases x <;> simp [mapOfO] at Hx ⊢
  simp only [mapOfO, isMapO]
  ihave #Hmm := isMapV_persistent_law_holds m kvs $$ Hmo
  ihave %Hmc := isMapV_concrete_law_holds m kvs $$ Hmm
  obtain ⟨gm, rfl⟩ := Hmc
  ihave ⟨Ha, %i, %Hai, #Hfree⟩ := isAlloc_Free h_heapAllocator_Free h_freelistAllocator_Free st.alloc $$ [Ha]
  · iframe Ha; iPkgInit
  rw [Hai]
  wp_auto
  by_cases hr : rel = .atomic
  · subst hr
    have hfa : fieldsAt S st.t st.path (.map kvs) = ins st.path := by simp [fieldsAt, Hfind]
    rw [hfa] at Hcard ⊢
    simp only [ElemRel.goName, _root_.decide_true]
    wp_auto
    unfold ownPath
    icases Hps with ⟨Hpf, Hpc⟩
    wp_apply h_Set_Insert s F ps (DFrac.own 1) st.path $$ [Hs Hpf] as ⟨Hs, Hpf⟩
    · iframe; ipureintro; exact LawB.cardLt_union_left _ _ _ Hcard
    wp_apply Hfree $$ %_ [Ha] as Ha
    · iframe; ihave ⟨-, Hf⟩ := (freeable_view_law_holds).1 _ kvs $$ Hmm; iexact Hf
    iapply HΦ
    iframe
    isplitr
    · iapply noErrs_nil
    unfold twOwn twCore ownPath
    iexists ps, sp
    rw [Hai]
    iframe
    iframe #
    ipureintro; exact Hwf
  · have hg : decide (rel.goName = go!"atomic") = false := by
      cases rel <;> first | exact absurd rfl hr | decide
    have hfa : fieldsAt S st.t st.path (.map kvs) = fieldsM S fs e st.path kvs := by
      cases rel <;> first | exact absurd rfl hr | simp [fieldsAt, Hfind]
    rw [hfa] at Hcard ⊢
    rw [hg]
    wp_auto
    icases IH with ⟨-, -, -, -, #HvM⟩
    wp_apply HvM $$ %w %sc %S %st %s %F %tp %fs %e %rel %_ %kvs [Hw Hps Hsp Ha Hs] as %errs ⟨Herrs, Hown⟩
    · iframe #
      isplitl [Hw Hps Hsp Ha Hs]
      · unfold twOwn twCore
        iexists ps, sp
        rw [Hai]
        iframe
        iframe #
        ipureintro; exact Hwf
      ipureintro; exact ⟨Hfind, Hc, Hcard⟩
    iunfold twOwn at Hown
    icases Hown with ⟨%ps', %sp', Hcore', Hps', Hsp', Ha', Hs'⟩
    rw [Hai]
    wp_apply Hfree $$ %_ [Ha'] as Ha'
    · iframe; ihave ⟨-, Hf⟩ := (freeable_view_law_holds).1 _ kvs $$ Hmm; iexact Hf
    iapply HΦ
    iframe
    unfold twOwn
    iexists ps', sp'
    rw [Hai]
    iframe

end proof

end smd
end EtcdGrove
end Perennial
