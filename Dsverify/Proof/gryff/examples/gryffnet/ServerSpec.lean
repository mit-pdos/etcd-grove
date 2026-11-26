/-
`Server(id)`'s spec (`KitServer.lean` proves it, `Server.wp_proof`): a defs module, so that the
commands' `main`s (`Mains.lean`) see it without importing the proof.
-/
module

public import Dsverify.Proof.gryff.Shares
public import Dsverify.Proof.gryff.Boot.Defs
public import Dsverify.GeneratedProof.gryff.examples.gryffnet
public import Dsverify.Proof.gryff.examples.gryffnet.Init

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace gryff.examples.gryffnet

open Perennial.gryff
open gryff.boot (gryffGlobals bootProph)

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]
variable [gA : examples.gryffnet.Assumptions] [net.rpc.Assumptions]
variable [RA : RpcHttpAddr GF] [net.http.Assumptions]

/-- **`Server(id)`**, server machine `id = i + 1` (`i < 4`: the master at `i = 0`, replica node
`i - 1` else): from what its machine's boot hands its `main` (the file header). -/
abbrev Server.spec : Prop :=
  ∀ (γ : GryffNames GF) (i : Nat), i < 4 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet ∗
      isPkgInit (PROP := IProp GF) pkg_id.net.rpc ∗ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗
      serverBoot (GF := GF) ∗
      ⌜threadBound GF ≤ 2 ^ 31 ∧ receiptBound GF ≤ 2 ^ 64⌝ ∗ serverShare γ i ∗
      (if i = 0 then iprop(True) else iprop(gryffGlobals ∗ bootProph)) ∗ threadTok }}
    (App (Val (@! gryff.examples.gryffnet.Server)) (Val #(W64 ((i + 1 : Nat) : Int))))
  {{ RET #(); True }}

end spec

end gryff.examples.gryffnet

end Perennial
