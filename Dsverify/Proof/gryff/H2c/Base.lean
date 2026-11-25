/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2c/Base.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2c: small helpers (`dlog` off, `Printf`)
-/
module

public import Dsverify.Proof.gryff.H2c.Helpers
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF] -- H1-R6 / N-1
variable [strconvA : strconv.Assumptions] -- N-5


set_option goose.wp.extras true

/-- `gryff`'s initialization includes `dlog`'s: `DLOG` is false. -/
theorem gryff_dlog :
    isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ⊢
      globalAddr gryff.src.dlog.DLOG ↦□ false := by
  iintro #H
  ihave #Hd : isPkgInit (PROP := IProp GF) pkg_id.gryff.src.dlog $$ []
  · solve_pkg_init
  iapply replica.dlog_init_access $$ Hd

/-- `dlog.Printf(f, args)` (a no-op). -/
theorem wp_dlog_Printf' (f : GoString) (v : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff }}
      (App (App (Val (@! gryff.src.dlog.Printf)) (Val #f)) (Val #v))
    {{ RET #(); True }} := by
  wp_start as #Hpkg
  ihave #Hd := gryff_dlog $$ Hpkg
  wp_auto
  wp_end

end

end Perennial.gryff.replica2

set_option hygiene false in
/-- A `dlog.Printf(fmt, args...)` call: the argument slice literal, then the no-op. -/
macro "h2c_printf" : tactic => `(tactic| (
  wp_apply wp_slice_literal (V := GoInterface) _
  isplitr
  · ipureintro; rfl
  iintro %_ ⟨-, -⟩
  wp_auto
  wp_apply wp_dlog_Printf'))

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]

/-- The broadcast optimization is off (`h2Fixed`). -/
theorem h2Fixed_bcastOpt (k : Fin 3) (gR h : Loc) :
    h2Fixed (GF := GF) k gR h ⊢ h.[src.gryff.EPaxosRMWHandler, go!"broadcastOptimizationEnabled"] ↦□ false := by
  unfold h2Fixed
  iintro ⟨%pS, %alS, %addrs, %st, %cPA, %cA, %cC, %cCS, %cPAR, %cPAO, %cAR, %cEx,
    -, -, -, -, -, -, -, -, -, #H, -⟩
  iexact H

end

end Perennial.gryff.replica2
