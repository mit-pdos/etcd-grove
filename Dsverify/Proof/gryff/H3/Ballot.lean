/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H3/Ballot.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit H3: the ballot helpers (`makeUniqueBallot`, `makeBallotLargerThan`, `isInitialBallot`),
stated generically in `GF` (the kernel is slow over the concrete `GF`).
-/
module

public import Dsverify.Proof.gryff.Replica2.Specs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2.h3

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.replica2
open gryff.src


section generic
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [π : NetProtoGS]
variable [sem : go.Semantics] [gryff_sem : gryff.Assumptions]

/-- The fields the ballot helpers read: `e.R`, `e.R.Replica`, its `Id`. -/
abbrev idAt (h : Loc) (k : Fin 3) : IProp GF :=
  iprop(∃ r gR : Loc, h.[src.gryff.EPaxosRMWHandler, go!"R"] ↦□ r ∗
    r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗ gR.[src.genericsmr.Replica, go!"Id"] ↦□ rid32 k)

theorem makeUniqueBallot.wp (h : Loc) (k : Fin 3) (b : w32) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ idAt h k }}
      (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!! go!"makeUniqueBallot")) (Val #b))
    {{ RET #(model.makeUniqueBallot (rid32 k) b); True }} := by
  wp_start as ⟨%r, %gR, Hr, HgR, Hid⟩
  wp_auto
  have e : (b <<< W64 4 ||| rid32 k) = model.makeUniqueBallot (rid32 k) b := by
    simp only [model.makeUniqueBallot]; rfl
  rw [e]; iapply HΦ; itrivial

theorem makeBallotLargerThan.wp (h : Loc) (k : Fin 3) (b : w32) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ idAt h k }}
      (App (Val (h @!! go.GoType.PointerType src.gryff.EPaxosRMWHandler.ty @!! go!"makeBallotLargerThan"))
        (Val #b))
    {{ RET #(model.makeBallotLargerThan (rid32 k) b); True }} := by
  wp_start as Hid
  wp_auto
  wp_apply makeUniqueBallot.wp h k $$ [Hid]
  · iexact Hid
  have e : model.makeUniqueBallot (rid32 k) (b.sshiftRight' (W64 4) + W32 1) =
      model.makeBallotLargerThan (rid32 k) b := by
    simp only [model.makeBallotLargerThan]; rfl
  rw [e]; iapply HΦ; itrivial

theorem isInitialBallot.wp (b : w32) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff }}
      (App (Val (@! gryff.isInitialBallot)) (Val #b))
    {{ RET #(model.isInitialBallot b); True }} := by
  wp_start
  wp_auto
  have e : decide (BitVec.sshiftRight' b (W64 4) = W32 0) = model.isInitialBallot b := by
    simp only [model.isInitialBallot]; rfl
  rw [e]; iapply HΦ; itrivial

end generic
end Perennial.gryff.replica2.h3
