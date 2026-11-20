/-
`typed.validatingObjectWalker.doList`: a member of the recursion cluster `typed.validatingObjectWalkerRec` (`validatingObjectWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `validatingObjectWalker__doListBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__doListBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.listValue
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
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

theorem typed.validatingObjectWalker.doList.wp_proofBody
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_listValue : typed.listValue.spec (GF := GF)) :
    typed.validatingObjectWalker.doList.specBody (GF := GF) := by
  unfold typed.validatingObjectWalker.doList.specBody typed.validatingObjectWalkerRec.specI
    typed.validatingObjectWalker.validate.specI typed.validatingObjectWalker.doList.specI
    typed.validatingObjectWalker.doMap.specI typed.validatingObjectWalker.visitListItems.specI
    typed.validatingObjectWalker.visitMapItems.specI
  iintro #IH
  iintro %w %sc %S %st %dq %x %tp %e %rel %ks %sp
  wp_start as ⟨Hown, Hv, #Hl, %Hfind, %Hc⟩
  have Hx : x = .null ∨ (listOfO (some x)).isSome := by
    unfold conforms at Hc
    cases x <;> simp_all [conformsB, listOfO]
  iunfold vwOwn at Hown
  icases Hown with ⟨Hcore, Hsp, Ha⟩
  iunfold vwCore at Hcore
  icases Hcore with ⟨%tr, Hw, #Htr, #Hsc, %Hwf⟩
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply h_listValue st.alloc st.value dq x $$ [Hv] as %l %err ⟨Hv, Hlo, %Herr⟩
  · iframe Hv; ipureintro; exact Hx
  rw [Herr.2 Hx]
  wp_auto
  rcases Hx with rfl | Hx
  · simp only [listOfO, isListO]
    icases Hlo with %Hlo
    subst Hlo
    wp_auto
    iapply HΦ
    iframe Hv
    isplitr
    · unfold noErrs ownErrs
      isplitr
      · iapply (ownSlice_nil (V := typed.ValidationError))
      · iapply ownSliceCap_nil
    iexists sp
    unfold vwOwn vwCore
    iframe Hsp Ha
    isplitl [Hw]
    · iexists tr
      iframe Hw
      iframe #
      ipureintro; exact Hwf
    ipureintro; intro; rfl
  · obtain ⟨vs, rfl⟩ : ∃ vs, x = .list vs := by
      cases x <;> simp [listOfO] at Hx ⊢
    simp only [listOfO, isListO]
    ihave #Hlv := isListV_persistent_law_holds l vs $$ Hlo
    ihave %Hlc := isListV_concrete_law_holds l vs $$ Hlv
    rcases Hlc with ⟨sl, rfl⟩ | ⟨pl, rfl⟩
    all_goals
      ihave ⟨Ha, %i, %Hai, #Hfree⟩ := isAlloc_Free h_heapAllocator_Free h_freelistAllocator_Free st.alloc $$ [Ha]
      · iframe Ha; iPkgInit
      rw [Hai]
      wp_auto
      icases IH with ⟨-, -, -, #HvL, -⟩
      wp_apply HvL $$ %w %sc %S %st %tp %e %rel %ks %_ %vs %sp [Hw Hsp Ha] as %errs ⟨Herrs, Hown⟩
      · iframe #
        isplitl [Hw Hsp Ha]
        · unfold vwOwn vwCore
          rw [Hai]
          iframe Hsp Ha
          iexists tr
          iframe Hw
          iframe #
          ipureintro; exact Hwf
        ipureintro; exact ⟨Hfind, Hc⟩
      iunfold vwOwn at Hown
      icases Hown with ⟨%sp', ⟨Hcore', Hsp', Ha'⟩, %Hsp'⟩
      rw [Hai]
      wp_apply Hfree $$ %_ [Ha'] as Ha'
      · iframe; ihave ⟨-, Hf⟩ := (freeable_view_law_holds).2.1 _ vs $$ Hlv; iexact Hf
      iapply HΦ
      iframe Herrs Hv
      iexists sp'
      unfold vwOwn
      rw [Hai]
      iframe
      ipureintro; exact Hsp'

end proof

end smd
end EtcdGrove
end Perennial
