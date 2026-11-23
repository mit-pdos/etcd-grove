/-
The proof of `log.Println` (`Spec.lean`), from Perennial's trusted model of `log`
(`Perennial/TrustedCode/log.lean`, `Println.impl`: it does nothing), as Perennial's
`log.Printf.wp_proof`.
-/
module

public import Dsverify.Proof.log.Spec

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : log.Assumptions]

theorem log.Println.wp_proof : log.Println.spec (GF := GF) := by
  intro arg xs dq Hxs
  wp_start as Hsl
  wp_end

end proof

end Perennial
