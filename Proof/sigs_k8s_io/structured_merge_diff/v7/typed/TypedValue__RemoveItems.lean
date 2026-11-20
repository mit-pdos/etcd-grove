/-
`typed.TypedValue.RemoveItems`: proved (Prove phase, 2026-11-20): the receiver's copy gets the value
`removeItemsWithSchema` returns (made persistent), its points-to persisted for `isTV`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__RemoveItems
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.removeItemsWithSchema
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

theorem typed.TypedValue.RemoveItems.wp_proof
    (h_removeItemsWithSchema : typed.removeItemsWithSchema.spec (GF := GF)) :
    typed.TypedValue.RemoveItems.spec (GF := GF) :=
    fun tv ip sc S t x R => by
  wp_start as ⟨Htv, #HR, %Hc'⟩
  iapply wp_fupd
  ihave #Htv := isTVv_persistent_law_holds tv sc S t x $$ Htv
  unfold isTVv
  icases Htv with ⟨%Hsc, #Hv, #Htr, #HS, %Hpre⟩
  obtain ⟨HWF, Hc⟩ := Hpre
  wp_auto
  rw [Hsc]
  wp_apply h_removeItemsWithSchema tv.value' DFrac.discard x ip sc R S tv.typeRef' t $$ [] as %v' ⟨-, Hv'⟩
  · iframe #; ipureintro; exact ⟨HWF, Hc⟩
  ihave Hv' : isValO v' (DFrac.own 1) (some (removeAt S t R x)) $$ [Hv']
  · simp only [isValO]; iexact Hv'
  imod isValO_persist_law_holds v' (DFrac.own 1) (some (removeAt S t R x)) $$ Hv' with Hv'
  imod (typedPointsto_dfractional _ _).dfractional_persist (DFrac.own 1) $$ tv with #Hp
  imodintro
  iapply HΦ
  iapply (isTV_isTVv_law_holds _ sc S t _).mpr
  iexists _
  iframe Hp
  unfold isTVv
  simp only [isValO]
  rw [Hsc]
  isplitr; · ipureintro; rfl
  isplitl [Hv']; · unfold removeItems; iexact Hv'
  iframe #
  ipureintro; exact ⟨HWF, Hc'⟩

end proof

end smd
end EtcdGrove
end Perennial
