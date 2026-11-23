/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/client/NodeGhost.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
L2 (notes/l2-design.md §5): each node's ghost, `client.NodeGhost` (a mutex and a prophecy, made
at the `client` package's initialization on every node; GHOST code in the fork), claimed for a
predicted node with the run's names before the node's first configuration acknowledgment
(`awaitConf`'s proof). What the claim gives: the registration (`sp.predReg`, which the
configuration port's acknowledgment carries) and the node's handle on its ghost for its later
resolutions (`client.nodeGhostOk`, persistent).

The spec is stated here for the adapter's proof (`awaitConf`); L2 proves it.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.Defs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]

/-- This node's ghost is claimed for the predicted node `n` (persistent): `n` is registered and
the package's `nodeGhost`'s mutex guards `n`'s prophecy and its half of `n`'s future words in
`sp.inv` (`client.nodeGhostB`, Spec/client/Ghost.lean); users only pass it on. -/
def client.nodeGhostOk (γ : sp.Names) (n : sp.PNode) : IProp netDistGF := client.nodeGhostB γ n

instance client.nodeGhostOk_persistent (γ : sp.Names) (n : sp.PNode) :
    Persistent (client.nodeGhostOk γ n) := by
  unfold client.nodeGhostOk; infer_instance

/-- **The claim** (a ghost step of the node, no code): with the client package initialized on
this node, the protocol's invariant, the node's exclusive right to claim its one ghost
(`client.ghostFresh`, Spec/client/Ghost.lean: handed out by the client package's first
initialization or taken from its package state with the node's own token; decision D90, R-E1)
and the node's registration token, the node registers its prediction. -/
abbrev client.claimGhost.spec : Prop :=
  ∀ (γ : sp.Names) (γc γm γl : GName) (n : sp.PNode),
  ⊢ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client -∗
    sp.inv γ γc γm γl -∗ client.ghostFresh -∗ sp.predTok γ n ={⊤}=∗
      sp.predReg γ n ∗ client.nodeGhostOk γ n

end spec

end Perennial.github_com.imdea_software.swiftpaxos
