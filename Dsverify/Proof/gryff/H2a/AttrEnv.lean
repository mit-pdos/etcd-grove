/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2a/AttrEnv.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2a: the fixed fields of the attribute helpers (`attrEnv`)
-/
module

public import Dsverify.Proof.gryff.H2.Env
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open Perennial.gryff.model (RState Copy LB Proposal Msg Ev Out Cmd Deps)
open Perennial.gryff.replica (XS rowOwn nSlots)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF] -- H1-R6 / N-1
variable [strconvA : strconv.Assumptions] -- N-5


set_option goose.wp.extras true

/-- The fixed fields `updateAttributes` / `updateConflicts` read. -/
def attrEnv (k : Fin 3) (r gR h : Loc) : IProp GF :=
  iprop(h.[src.gryff.EPaxosRMWHandler, go!"R"] ↦□ r ∗ r.[src.gryff.Replica, go!"Replica"] ↦□ gR ∗
    gR.[src.genericsmr.Replica, go!"Id"] ↦□ rid32 k ∗ gR.[src.genericsmr.Replica, go!"N"] ↦□ W64 3 ∗
    □ h2Fixed k gR h)

instance attrEnv_persistent (k : Fin 3) (r gR h : Loc) : Persistent (attrEnv (GF := GF) k r gR h) := by
  unfold attrEnv; infer_instance

end

end Perennial.gryff.replica2
