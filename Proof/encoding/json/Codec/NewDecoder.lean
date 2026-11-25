/-
The proof of `NewDecoder.spec` (`Spec/encoding/json/Codec/NewDecoder.lean`) at the model's decoder
representation (`decRepModel`, `DecoderModel.lean`): `&Decoder{r: r}`, its buffer nil.
-/
module

public import Spec.encoding.json.Codec.NewDecoder
public import Proof.encoding.json.DecoderModel

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

attribute [local instance] decRepModel

theorem NewDecoder.wp_proof : NewDecoder.spec (GF := GF) (hG := hG) := by
  intro r I
  wp_start as ⟨%Hr, HI⟩
  cases r with
  | nil => exact absurd rfl Hr
  | ok ri =>
  wp_auto
  iapply HΦ
  rw [decRepModel_decOk]
  unfold decOkModel
  iexists (Decoder.mk (GoInterface.ok ri) slice.nil 0 0 0 GoInterface.nil false), [], []
  iframe
  isplitl []
  · iapply ownSlice_nil
  isplitl []
  · iapply ownSliceCap_nil
  ipureintro
  refine ⟨rfl, rfl, rfl, ⟨Int.le_refl _, Int.le_refl _, by simp, ?_⟩, rfl⟩
  show 3 * sint.Z (slice.nil : GoSlice).cap < 2 ^ 63
  simp only [slice.nil]; decide

end proof

end encoding.json
end Perennial
