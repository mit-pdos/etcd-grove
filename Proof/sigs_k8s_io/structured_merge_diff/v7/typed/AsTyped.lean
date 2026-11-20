/-
`typed.AsTyped`: proved (Prove phase, 2026-11-20): the new `TypedValue` validates (no options; the
value conforms), and its points-to is made persistent for `isTV`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.AsTyped
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__Validate_ptr
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

theorem typed.AsTyped.wp_proof
    (h_TypedValue_Validate_ptr : typed.TypedValue.Validate_ptr.spec (GF := GF)) :
    typed.AsTyped.spec (GF := GF) :=
    fun v x sc S tr t => by
  wp_start as ⟨#Hv, #Hsc, #Htr, %Hpre⟩
  wp_auto
  obtain ⟨HWF, Hc⟩ := Hpre
  wp_apply h_TypedValue_Validate_ptr _ (DFrac.own 1) ⟨v, tr, sc⟩ sc S t x DFrac.discard slice.nil
    DFrac.discard $$ [«$r0»] as %err ⟨Hp, -, -, %He⟩
  · iframe «$r0»
    isplitr
    · unfold isTVu; iframe #; ipureintro; exact ⟨rfl, HWF⟩
    isplitr
    · iapply ownSlice_nil
    ipureintro; exact Hc
  subst He
  imod (typedPointsto_dfractional _ _).dfractional_persist (DFrac.own 1) $$ Hp with #Hp
  wp_auto
  iapply HΦ
  isplitr; · ipureintro; rfl
  iapply (isTV_isTVv_law_holds _ sc S t x).mpr
  iexists _
  iframe Hp
  unfold isTVv
  simp only
  iframe #
  ipureintro; exact ⟨HWF, Hc⟩

end proof

end smd
end EtcdGrove
end Perennial
