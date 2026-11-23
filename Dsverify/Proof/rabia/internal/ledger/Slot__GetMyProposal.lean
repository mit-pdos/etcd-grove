/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/ledger/Slot__GetMyProposal.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/internal/ledger.(*Slot).GetMyProposal`.
-/
module

public import Dsverify.Proof.rabia.internal.ledger.Basics

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.ledger

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model rabia.internal.message

set_option linter.unusedSectionVars false

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.ledger.Assumptions]

theorem Slot.GetMyProposal.wp_proof : Slot.GetMyProposal.spec (GF := GF) :=
    fun s pv => by
  wp_start as H
  iNamed H
  wp_auto
  iapply HΦ
  iframe Hmprep
  unfold slotPriv
  iexists mp
  iframe Hph Hrd Hmp Hmprep Hmy

end proof
end Perennial.rabia.internal.ledger
