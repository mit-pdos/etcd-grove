/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/H2a/Link.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit H2a: the frozen `handlePreAccept.wp`'s statement, proved (`Replica2/Specs.lean` cannot import
the proof: the hub links `handlePreAccept.wp := handlePreAccept_wp_link …` at merge, as for
`epaxosOwn_inst_open'`)
-/
module

public import Dsverify.Proof.gryff.H2.PreAccept
public import Dsverify.GeneratedProof.gryff.examples.gryffnet

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.replica2

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [fa : src.fastrpc.Assumptions] [wire.BufioSpecs GF]
variable [binA : wire.BinaryVarintHyps GF] -- H1-R6 / N-1
variable [strconvA : strconv.Assumptions] -- N-5

variable [pD : GryffPartiDeps (GF := GF)] in
/-- **`handlePreAccept.wp`** (`Replica2/Specs.lean`), same statement. -/
theorem handlePreAccept_wp_link (γ : GryffNames GF) (ρ : Repl2Names) (k : Fin 3) (r h : Loc)
    (m : model.PreAcceptM) : epHandlerSpec γ ρ k r h go!"handlePreAccept" (.preAccept m) := by
  intro p t s s' outs hstep
  iintro %Φ ⟨#Hpkg, #Hrep, Hown, Hpend, Hh, Hmsg⟩ HΦ
  iapply (handlePreAccept_wp' γ ρ k r h p m t s s' outs hstep) $$ [Hown Hpend Hh Hmsg] HΦ
  iframe # ∗

end

end Perennial.gryff.replica2
