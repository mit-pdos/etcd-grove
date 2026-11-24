/-
The proof of `token.IsExported` (`Net/Spec/go/token/IsExported.lean`): the model's ASCII branch.
-/
module

public import Net.Spec.go.token.IsExported
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace go''.token

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : go''.token.Assumptions]

theorem IsExported.wp_proof : IsExported.spec (GF := GF) (hG := hG) := by
  intro c rest hc
  wp_start
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  have hne : W64 (c :: rest).length ≠ W64 0 := by
    simp at Hl ⊢; word
  rw [decide_eq_false hne]
  wp_auto
  have h1 : uint.Z c < uint.Z (W8 128) := by
    have := hc.2; simp at this ⊢; omega
  rw [decide_eq_true h1]
  wp_auto
  rw [decide_eq_true hc.1]
  wp_auto
  rw [decide_eq_true hc.2]
  iapply HΦ; itrivial

end proof

end go''.token
end Perennial
