/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/OrchSpec.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`OrchOk` (Spec/swiftnet/Interface.lean): the orchestrator's spec at node 0 (`OrchSpec`): the test
package's initialization (`adapter.initialize.wp_proof`, from the SwiftPaxos packages'
initializers, `SwiftInits`: group C's `adapter.swiftInits` at `pkgStates`), `New`
(`orch.New.wp_proof`), `Gen` and `Start` (`orch.Gen.wp_proof`, `orch.Start.wp_proof`).

`orch_ok_of` takes the package states and their initializers as hypotheses; `Proof/swiftnet/Orch.lean`
gives `orch_ok : OrchOk pkgStates` with group C's `adapter.swiftInits`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.OrchNew
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.OrchGen
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientInit

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- The orchestrator's hypotheses (group C's): the SwiftPaxos packages' initializers at the
package states `S`, at every heap and Go context of node 0. -/
def OrchHyps [GoGlobalContext] (S : SwiftNetPkgStates) : Prop :=
  ∀ (hG : HeapGS .hasLC netDistGF) (s : go.Semantics),
    ∀ [examples.swiftnet.Assumptions] [net.FieldAssumptions],
    letI := @S netDistGF hG s
    adapter.SwiftInits

/-- **`OrchOk`**, from the package states' initializers. -/
theorem orch_ok_of [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF] (S : SwiftNetPkgStates)
    (H : OrchHyps S) : OrchOk S := by
  intro γ hG s hGG hA ip hip hnet
  obtain ⟨hA1, hA2, hA3⟩ := hA
  letI := @S netDistGF hG s
  have hI := H hG s
  subst hGG
  exact ⟨{
    wp_initialize' := fun g hg => adapter.initialize.wp_proof hI g hg
    wp_New := fun sl => orch.New.wp_proof γ sl
    wp_Gen := fun c j => orch.Gen.wp_proof orch.digits.wp_proof c j
    wp_Start := fun c => orch.Start.wp_proof c }⟩

end Perennial.github_com.imdea_software.swiftpaxos
