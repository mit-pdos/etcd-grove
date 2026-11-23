/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/Claim.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
L2: the claim of the node's ghost (`client.claimGhost.spec`, Spec/client/NodeGhost.lean): the
node's fresh ghost (`client.ghostFresh`) registers its prediction (`sp.pred_register`, the
prophecy's values as its future words) and the mutex becomes the node's ghost lock
(`client.nodeLockR`). (The lab's `client.ghostFresh_take`, the claim off a replica node with
the node's address token, is gone: every node's boot thread gets the fresh ghost,
Proof/client/Pkg.lean.)
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
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [sync.Assumptions]

/-- **The claim** (`client.claimGhost.spec`): the node's fresh ghost (`client.ghostFresh`: its
prophecy and its zero mutex) registers the node's prediction (`sp.pred_register`, the
prophecy's values as its future words) and its mutex becomes the node's ghost lock
(`client.nodeLockR`). -/
theorem client.claimGhost.wp_proof : client.claimGhost.spec (hG := hG) := by
  intro γ γc γm γl n
  iintro #Hpkg #Hinv Hfr Htok
  iunfold client.ghostFresh at Hfr
  icases Hfr with ⟨%g, %p, %pvs, #Hg, %Hne, #Hp, Hpr, Hmu⟩
  imod (sp.pred_register (γ := γ) (γc := γc) (γm := γm) (γl := γl) ⊤
    (by solve_ndisj) n (pvs.map sp.valW)) $$ [Htok] with ⟨#Hreg, Hw⟩
  · iframe Hinv Htok
  imod sync.init_Mutex (client.nodeLockR γ n p) ⊤ _ $$ Hmu [Hpr Hw]
    with #Hmu
  · inext
    iunfold client.nodeLockR
    iexists pvs
    iframe
  imodintro
  iframe Hreg
  iunfold client.nodeGhostOk
  iunfold client.nodeGhostB
  iframe Hreg
  iexists g
  iframe Hg
  iunfold client.isNodeGhost
  iexists p
  iframe Hp Hmu
  ipureintro; exact Hne

end proof

end Perennial.github_com.imdea_software.swiftpaxos
