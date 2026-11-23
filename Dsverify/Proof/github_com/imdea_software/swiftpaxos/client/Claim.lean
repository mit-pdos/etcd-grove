/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/Claim.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
L2: the claim of the node's ghost (`client.claimGhost.spec`, Spec/client/NodeGhost.lean): the
node's fresh ghost (`client.ghostFresh`) registers its prediction (`sp.pred_register`, the
prophecy's values as its future words) and the mutex becomes the node's ghost lock
(`client.nodeLockR`). Off a replica node the fresh ghost is taken from the client package's
state with the node's own address token (`client.ghostFresh_take`; decision D90, R-E1).
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

omit [sync.Assumptions] in
/-- **Off a replica node, the node's own address token takes its fresh ghost** from the client
package's state (Proof/client/Pkg.lean): the invariant gives up the unclaimed ghost and keeps
the token (a second taking would need a second token). -/
theorem client.ghostFresh_take
    (hpkg : isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ⊢
      client.pkgSt)
    (hrn : ¬ swift.replicaNode (netIp (L := hG.goose_localGS) (GF := netDistGF))) :
    ⊢ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client -∗
      addrTok (client.keyAddr (netIp (L := hG.goose_localGS) (GF := netDistGF)))
        ={⊤}=∗ client.ghostFresh := by
  iintro #Hpkg Htok
  ihave #Hst := hpkg $$ Hpkg
  iunfold client.pkgSt at Hst
  rw [if_neg hrn]
  icases Hst with ⟨%g, %p, #Hg, %Hne, #Hp, #Hi⟩
  iinv Hi with Hc Hclose
  icases Hc with (Hu | Htok')
  · imod Hclose $$ [Htok] with -
    · inext; iright; iexact Htok
    iunfold client.ghostUnclaimed at Hu
    icases Hu with ⟨%pvs, >Hpr, >Hmu⟩
    imodintro
    iunfold client.ghostFresh
    iexists g, p, pvs
    iframe Hg Hp Hpr Hmu
    ipureintro; exact Hne
  · -- the token is unique: the invariant cannot hold it already
    ihave Hf : iprop(▷ False) $$ [Htok Htok']
    · inext
      iapply (client.addrTokG_excl netDistGS _)
      isplitl [Htok]
      · iexact Htok
      · iexact Htok'
    icases Hf with >Hf
    iexfalso
    iexact Hf

end proof

end Perennial.github_com.imdea_software.swiftpaxos
