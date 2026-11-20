/-
`typed.TypedValue.Validate`: proved (Prove phase, 2026-11-20): no options (the range loop runs
zero times), the walker validates a conforming value with no errors, then goes back to its pool.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__Validate
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__walker
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__finished
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.validatingObjectWalker__validate
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsAPure
public import Proof.sigs_k8s_io.structured_merge_diff.v7.typed.LawProofsBPers

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

theorem typed.TypedValue.Validate.wp_proof
    (h_TypedValue_walker : typed.TypedValue.walker.spec (GF := GF))
    (h_validatingObjectWalker_finished : typed.validatingObjectWalker.finished.spec (GF := GF))
    (h_validatingObjectWalker_validate : typed.validatingObjectWalker.validate.spec (GF := GF)) :
    typed.TypedValue.Validate.spec (GF := GF) :=
    fun tv sc S t x dq opts dqo => by
  wp_start as ⟨Htv, Hopts, %Hc⟩
  unfold isTVu
  icases Htv with ⟨%Hsc, Hv, #Htr, #HS, %HWF⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_method_call
  try wp_auto
  wp_apply h_TypedValue_walker tv S t $$ [] as %w ⟨%a, Hown⟩
  · rw [Hsc]; iframe #; ipureintro; exact HWF
  ihave %hl := ownSlice_len _ _ _ $$ Hopts
  ihave HI : (∃ j : w64, "i" ∷ i_ptr ↦ j ∗ "%Hj" ∷ ⌜j = W64 0⌝ : IProp GF) $$ [i]
  · iexists _; iframe; ipureintro; rfl
  wp_for HI
  subst Hj
  wp_if_destruct
  · exfalso; simp at hl; word
  wp_apply h_validatingObjectWalker_validate w tv.schema' S ⟨tv.value', t, a⟩ dq x func.nil
    $$ [Hown Hv] as %errs ⟨Herrs, Hv, Hown⟩
  · iframe
    isplitr
    · unfold prefixOk; ileft; ipureintro; rfl
    ipureintro; exact ⟨LawA.conforms_find S t x Hc, Hc⟩
  ihave %Hlen := noErrs_len $$ Herrs
  rw [show decide (errs.len = W64 0) = true by simp; word]
  wp_auto
  wp_apply h_validatingObjectWalker_finished w tv.schema' S ⟨tv.value', t, a⟩ $$ [Hown]
  · iexact Hown
  iapply HΦ
  iframe
  ipureintro; rfl

end proof

end smd
end EtcdGrove
end Perennial
