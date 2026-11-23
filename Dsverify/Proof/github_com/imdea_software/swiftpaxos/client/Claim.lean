/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/Claim.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
L2: the claim of the node's prophecy (`client.claimGhost.spec`, Spec/client/NodeGhost.lean): the
node's fresh prophecy of its kind (`client.freshOf n`) registers its prediction (`sp.pred_register`,
the prophecy's values' words as its future words) and goes into an invariant with the node's half
(`client.nodeLockR`). Every node's boot thread gets both packages' fresh prophecies
(Proof/client/Pkg.lean, examples/swiftnet/BootLinked.lean).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Pkg
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.L2Laws
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.NodeGhost

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [sync.Assumptions]

/-- **The claim** (`client.claimGhost.spec`): the node's fresh prophecy of its kind
(`client.freshOf n`) registers the node's prediction (`sp.pred_register`, the prophecy's values'
words as its future words), and an invariant ties them (`client.nodeLockR`). -/
theorem client.claimGhost.wp_proof : client.claimGhost.spec (hG := hG) := by
  intro γ γc γm γl n
  iintro #Hpkg #Hinv Hfr Htok
  iunfold client.freshOf at Hfr
  iunfold client.prophFresh at Hfr
  icases Hfr with ⟨%p, %pvs, #Hp, Hpr⟩
  imod (sp.pred_register (γ := γ) (γc := γc) (γm := γm) (γl := γl) ⊤
    (by solve_ndisj) n (pvs.flatMap sp.valWs)) $$ [Htok] with ⟨#Hreg, Hw⟩
  · iframe Hinv Htok
  imod inv_alloc client.nodeProphN ⊤ (client.nodeLockR γ n p) $$ [Hpr Hw] with #Hi
  · inext
    iunfold client.nodeLockR
    iexists pvs
    iframe
  imodintro
  iframe Hreg
  iunfold client.nodeGhostOk
  iunfold client.nodeGhostB
  iframe Hreg
  iexists p
  iframe Hp Hi

end proof

end Perennial.github_com.imdea_software.swiftpaxos
