/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/config/CalcConstants.lean`, run `rabia-r1wake-1`.)

The proof of `(*Config).CalcConstants` (`Config.CalcConstants.spec`).
-/
module

public import Dsverify.Proof.rabia.internal.config.Spec

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.config

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.config.Assumptions]

theorem Config.CalcConstants.wp_proof : Config.CalcConstants.spec (GF := GF) := by
  intro c v
  wp_start as Hc
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hc
  iStructNamed Hc
  wp_auto
  wp_if_destruct
  · skip
    iapply HΦ
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
    simp only [Hif, ↓reduceIte]
    iexact NClientRequests
  · skip
    iapply HΦ
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
    simp only [Hif, ↓reduceIte]
    iexact NClientRequests

end proof

end Perennial.rabia.internal.config
