/-
`io.ReadFull.wp_proofLt`: Perennial's `io.ReadFull.wp_proof` (over `io.ReadAtLeast.wp_proof`), the
proof of `io.ReadFull.specLt` (`ConnRead.lean`). Until the pin bump to Perennial `580868e54`
(2026-11-24, which has branch `readatleast-prefix`) a local copy of that branch's proofs.
-/
module

public import Dsverify.Proof.rabia.examples.rabianet.ConnRead
public import Perennial.Proof.io.ReadAtLeast
public import Perennial.Proof.io.ReadFull

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.rabia.examples.rabianet

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.io.Assumptions]

theorem io.ReadFull.wp_proofLt : io.ReadFull.specLt (GF := GF) (hG := hG) :=
  _root_.Perennial.io.ReadFull.wp_proof _root_.Perennial.io.ReadAtLeast.wp_proof

end proof

end Perennial.rabia.examples.rabianet
