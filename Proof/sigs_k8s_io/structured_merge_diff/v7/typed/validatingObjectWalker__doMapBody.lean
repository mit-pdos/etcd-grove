/-
`typed.validatingObjectWalker.doMap`: a member of the recursion cluster `typed.validatingObjectWalkerRec` (`validatingObjectWalkerRec.lean`); its proof is the
projection of the cluster's (its body is `validatingObjectWalker__doMapBody.lean`).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__doMapBody
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.heapAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.freelistAllocator__Free
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.mapValue
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers
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

theorem typed.validatingObjectWalker.doMap.wp_proofBody
    (h_heapAllocator_Free : value.heapAllocator.Free.spec (GF := GF))
    (h_freelistAllocator_Free : value.freelistAllocator.Free.spec (GF := GF))
    (h_mapValue : typed.mapValue.spec (GF := GF)) :
    typed.validatingObjectWalker.doMap.specBody (GF := GF) := by
  unfold typed.validatingObjectWalker.doMap.specBody typed.validatingObjectWalkerRec.specI
    typed.validatingObjectWalker.validate.specI typed.validatingObjectWalker.doList.specI
    typed.validatingObjectWalker.doMap.specI typed.validatingObjectWalker.visitListItems.specI
    typed.validatingObjectWalker.visitMapItems.specI
  iintro #IH
  iintro %w %sc %S %st %dq %x %tp %fs %e %rel
  wp_start as ⟨Hown, Hv, #Hm, %Hfind, %Hc⟩
  have Hx : some x = some .null ∨ (mapOfO (some x)).isSome := by
    unfold conforms at Hc
    cases x <;> simp_all [conformsB, mapOfO]
  iunfold vwOwn at Hown
  icases Hown with ⟨%sp, Hcore, Hsp, Ha⟩
  iunfold vwCore at Hcore
  icases Hcore with ⟨%tr, Hw, #Htr, #Hsc, %Hwf⟩
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply h_mapValue st.alloc st.value dq (some x) $$ [Hv] as %m %err ⟨Hv, Hmo, %Herr⟩
  · simp only [isValO]; iframe Hv; ipureintro; exact Hx
  simp only [isValO]
  rw [Herr.2 Hx]
  wp_auto
  rcases Hx with Hx | Hx
  · cases Hx
    simp only [mapOfO, isMapO]
    icases Hmo with %Hmo
    subst Hmo
    wp_auto
    iapply HΦ
    iframe Hv
    isplitr
    · iapply noErrs_nil
    unfold vwOwn vwCore
    iexists sp
    iframe Hsp Ha
    iexists tr
    iframe Hw
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
  icases IH with ⟨-, -, -, -, #HvM⟩
  wp_apply HvM $$ %w %sc %S %st %tp %fs %e %rel %_ %kvs [Hw Hsp Ha] as %errs ⟨Herrs, Hown⟩
  · iframe #
    isplitl [Hw Hsp Ha]
    · unfold vwOwn vwCore
      iexists sp
      rw [Hai]
      iframe Hsp Ha
      iexists tr
      iframe Hw
      iframe #
      ipureintro; exact Hwf
    ipureintro; exact ⟨Hfind, Hc⟩
  iunfold vwOwn at Hown
  icases Hown with ⟨%sp', Hcore', Hsp', Ha'⟩
  rw [Hai]
  wp_apply Hfree $$ %_ [Ha'] as Ha'
  · iframe; ihave ⟨-, Hf⟩ := (freeable_view_law_holds).1 _ kvs $$ Hmm; iexact Hf
  iapply HΦ
  iframe Herrs Hv
  unfold vwOwn
  iexists sp'
  rw [Hai]
  iframe

end proof

end smd
end EtcdGrove
end Perennial
