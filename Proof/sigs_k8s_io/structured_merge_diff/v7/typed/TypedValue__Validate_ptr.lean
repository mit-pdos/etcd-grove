/-
`typed.TypedValue.Validate_ptr`: proved (Prove phase, 2026-11-20): loads the receiver, then
`Validate`.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__Validate_ptr
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.TypedValue__Validate

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

theorem typed.TypedValue.Validate_ptr.wp_proof
    (h_TypedValue_Validate : typed.TypedValue.Validate.spec (GF := GF)) :
    typed.TypedValue.Validate_ptr.spec (GF := GF) :=
    fun p dqp tv sc S t x dq opts dqo => by
  wp_start as ⟨Hp, Htv, Hopts, %Hc⟩
  try wp_auto
  wp_apply h_TypedValue_Validate tv sc S t x dq opts dqo $$ [Htv Hopts] as %err ⟨Hv, Hopts, %He⟩
  · iframe; ipureintro; exact Hc
  iapply HΦ
  iframe
  ipureintro; exact He

end proof

end smd
end EtcdGrove
end Perennial
