/-
Ported from dsverify-lab examples/swiftpaxos/proof/Spec/swift/NewClient.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`swift.NewClient(b, N)`: SwiftPaxos's client on a connected buffer client: its message sets,
its handler (`handleMsgs`) and a reader per connected replica (`RegisterRPCTable`).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.Defs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.NodeGhost

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section spec
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions]

/-- From a connected client (with `N` the membership's size) and the protocol's sequence
number 0 of its id, its node's claimed ghost (`client.nodeGhostOk`, L2: client `cid - 1` is
predicted node `cl (cid - 1)`) and the registration of every prediction (`sp.allPredsReg`,
which `own_state` carries; stage 2): the client ready for its commands from sequence number 0. -/
abbrev swift.NewClient.spec : Prop :=
  ∀ (b : Loc) (γ : sp.Names) (γc γm γl : GName) (cid : w32) (N : Nat),
  {{ isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift ∗
      client.connected b γ γc γm cid N ∗ sp.inv γ γc γm γl ∗ sp.clientSeq γ cid 0 ∗
      client.nodeGhostOk γ (sp.PNode.cl (cid.toNat - 1)) ∗ sp.allPredsReg γ γc }}
    (App (App (Val (@! swift.NewClient)) (Val #b)) (Val #(W64 N)))
  {{ (c : Loc), RET #c; client.ready b γ γc γm γl cid 0 }}

end spec

end Perennial.github_com.imdea_software.swiftpaxos
