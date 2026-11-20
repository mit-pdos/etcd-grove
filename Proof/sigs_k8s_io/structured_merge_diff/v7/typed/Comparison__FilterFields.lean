/-
`typed.Comparison.FilterFields`: proved (Prove phase, 2026-11-20): the argument is nil (the scope), so it
returns the comparison unchanged.
-/
module

public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.Comparison__FilterFields

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

theorem typed.Comparison.FilterFields.wp_proof :
    typed.Comparison.FilterFields.spec (GF := GF) :=
    fun c C filter => by
  wp_start as ⟨Hc, %Hf⟩
  subst Hf
  wp_auto
  iapply HΦ
  iexact Hc

end proof

end smd
end EtcdGrove
end Perennial
