/-
`typed.TypedValue.RemoveItems_ptr`: proved (Prove phase, 2026-11-20): the receiver's persistent
points-to (`isTV`) loaded, then `RemoveItems`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__RemoveItems_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__RemoveItems
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

theorem typed.TypedValue.RemoveItems_ptr.wp_proof
    (h_TypedValue_RemoveItems : typed.TypedValue.RemoveItems.spec (GF := GF)) :
    typed.TypedValue.RemoveItems_ptr.spec (GF := GF) :=
    fun tp ip sc S t x R => by
  wp_start as ⟨Htv, #HR, %Hc⟩
  ihave H2 := (isTV_isTVv_law_holds tp sc S t x).mp $$ Htv
  icases H2 with ⟨%tv, #Hp, #Htv⟩
  wp_auto
  wp_apply h_TypedValue_RemoveItems tv ip sc S t x R $$ [] as %p Hp'
  · iframe #; ipureintro; exact Hc
  iapply HΦ
  iexact Hp'

end proof

end smd
end EtcdGrove
end Perennial
