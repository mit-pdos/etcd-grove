/-
`typed.TypedValue.Compare_ptr`: proved (Prove phase, 2026-11-20): the receiver's persistent
points-to (`isTV`) loaded, then `Compare`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__Compare_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__Compare
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

theorem typed.TypedValue.Compare_ptr.wp_proof
    (h_TypedValue_Compare : typed.TypedValue.Compare.spec (GF := GF)) :
    typed.TypedValue.Compare_ptr.spec (GF := GF) :=
    fun lp q sc S t l r => by
  wp_start as ⟨Htv, #Hq, %Hsz⟩
  ihave H2 := (isTV_isTVv_law_holds lp sc S t l).mp $$ Htv
  icases H2 with ⟨%tv, #Hp, #Htv⟩
  wp_auto
  wp_apply h_TypedValue_Compare tv q sc S t l r $$ [] as %c %err ⟨%He, Hc⟩
  · iframe #; ipureintro; exact Hsz
  iapply HΦ
  iframe
  ipureintro; exact He

end proof

end smd
end EtcdGrove
end Perennial
