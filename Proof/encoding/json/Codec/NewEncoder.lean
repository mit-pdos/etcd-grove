/-
The proof of `NewEncoder` (`Spec/encoding/json/Codec/NewEncoder.lean`) at the model's encoder
representation (`encRepModel`, `EncoderModel.lean`): the model's `&Encoder{w: w, escapeHTML: true}`.
-/
module

public import Spec.encoding.json.Codec.NewEncoder
public import Proof.encoding.json.EncoderModel

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace encoding.json

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : encoding.json.Assumptions]

attribute [local instance] encRepModel

theorem NewEncoder.wp_proof : NewEncoder.spec (GF := GF) (hG := hG) := by
  intro w
  wp_start as #Hpkg
  wp_auto
  iapply HΦ
  rw [encRepModel_encOk]
  unfold encOkModel
  iexists _
  iframe
  ipureintro
  exact ⟨rfl, rfl, rfl, rfl⟩

end proof

end encoding.json
end Perennial
