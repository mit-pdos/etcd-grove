/- Lean-first (no Rocq counterpart).

Proof of `Spec/github_com/anishathalye/porcupine/LinearizationInfo__PartialLinearizations.lean`.
-/
module

public import Spec.github_com.anishathalye.porcupine.LinearizationInfo__PartialLinearizations

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace porcupine

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.anishathalye.porcupine

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

theorem LinearizationInfo.PartialLinearizations.wp_proof :
    LinearizationInfo.PartialLinearizations.spec (GF := GF) (hG := hG) := by
  intro li dq info
  wp_start as Hli
  icases (typedPointsto_not_null_dup _ _ _) $$ Hli with ⟨Hli, %Hlin⟩
  iStructNamed Hli
  (try wp_auto)
  iapply HΦ
  iapply typedPointsto_combine li _ dq Hlin
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end porcupine
end EtcdGrove
end Perennial
