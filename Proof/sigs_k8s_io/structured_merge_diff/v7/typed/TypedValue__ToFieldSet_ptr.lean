/-
`typed.TypedValue.ToFieldSet_ptr`: proved (Prove phase, 2026-11-20): the receiver's persistent
points-to (`isTV`) loaded, then `ToFieldSet`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__ToFieldSet_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__ToFieldSet
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

theorem typed.TypedValue.ToFieldSet_ptr.wp_proof
    (h_TypedValue_ToFieldSet : typed.TypedValue.ToFieldSet.spec (GF := GF)) :
    typed.TypedValue.ToFieldSet_ptr.spec (GF := GF) :=
    fun p sc S t x => by
  wp_start as ⟨Htv, %Hsz⟩
  ihave H2 := (isTV_isTVv_law_holds p sc S t x).mp $$ Htv
  icases H2 with ⟨%tv, #Hp, #Htv⟩
  wp_auto
  wp_apply h_TypedValue_ToFieldSet tv sc S t x $$ [] as %s %err ⟨%He, Hs⟩
  · iframe #; ipureintro; exact Hsz
  iapply HΦ
  iframe
  ipureintro; exact He

end proof

end smd
end EtcdGrove
end Perennial
