/-
`typed.validatingObjectWalker.doScalar`: not proved yet (`sorry`): the stage's Prove step, after the freeze
(notes/smd-plan.md). Draft (2026-11-19).
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__doScalar
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validateScalar

public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsA

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

theorem typed.validatingObjectWalker.doScalar.wp_proof
    (h_validateScalar : typed.validateScalar.spec (GF := GF)) :
    typed.validatingObjectWalker.doScalar.spec (GF := GF) := fun w sc S st dq x tp s => by
  wp_start as ⟨Hown, Hv, #Htp, %Hfind, %Hc⟩
  have hok : scalarOk s x = true := by
    unfold conforms at Hc
    cases x <;> simp [conformsB, Hfind] at Hc ⊢ <;> exact Hc
  unfold vwOwn vwCore
  icases Hown with ⟨%sp, ⟨%tr, Hw, #Htr, #Hsc, %Hwf⟩, Hsp, Ha⟩
  wp_auto
  wp_apply h_validateScalar tp s st.value dq (some x) (go!"") $$ [Hv] as %errs ⟨Hv, Herrs⟩
  · iframe #; unfold isValO; iframe Hv; ipureintro; exact hok
  unfold isValO noErrs ownErrs
  icases Herrs with ⟨Hes, -⟩
  ihave %Hl := ownSlice_len $$ Hes
  have hz : ¬ (sint.Z (W64 0) < sint.Z errs.len) := by
    simp only [List.length_nil] at Hl
    have : sint.Z (W64 0) = 0 := rfl
    word
  rw [decide_eq_false hz]
  wp_auto
  iapply HΦ
  iframe Hv
  isplitr
  · isplitr
    · iapply (ownSlice_nil (V := typed.ValidationError))
    · iapply ownSliceCap_nil
  iexists sp
  iframe Hsp Ha
  iexists tr
  iframe Hw
  iframe #
  ipureintro; exact Hwf

end proof

end smd
end EtcdGrove
end Perennial
