/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/Parts.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The parts of `goal_spec` (`Spec/swiftnet/Interface.lean`'s `goal_spec_of`): the start
(`start_ok`, Start.lean), the orchestrator (`orch_ok`, Orch.lean), the client nodes
(`client_node_ok`, ClientNodeLink.lean, over its callees' linked specs `client_node_hyps`,
below) and the server nodes (`servers_ok`, ServersLink.lean, over L2's claim `claim_hyp`,
ClaimLink.lean), and `goal_spec_parts`, which assembles them.
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.examples.swiftnet.Interface
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.PkgState
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.Start
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.Orch
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientNodeLink
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClaimLink
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ServersLink
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Link

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

-- The codec of the linked results (decision D6, Proof/swiftnet/KitLike.lean): `kitCodecC`.
attribute [local instance 2000] examples.swiftnet.kitCodecC

section link
variable [GoGlobalContext]

/-- The swift and defs packages' facts the client's handler uses (change log C6), from their
package states off a replica node. -/
theorem client_pkg_facts (hG : HeapGS .hasLC netDistGF) (s : go.Semantics)
    (hnr : ¬ swift.replicaNode (netIp (L := hG.goose_localGS) (GF := netDistGF))) :
    letI := @pkgStates _ netDistGF hG s
    swift.handler.ClientPkgFacts (hG := hG) := by
  letI := @pkgStates _ netDistGF hG s
  have hsw : isPkgInit (PROP := IProp netDistGF)
      pkg_id.github_com.imdea_software.swiftpaxos.swift ⊢ swift.pkgSt := by
    with_unfolding_all exact isPkgInit_access (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.swift
  have hdf : isPkgInit (PROP := IProp netDistGF)
      pkg_id.github_com.imdea_software.swiftpaxos.replica.defs ⊢ defs.pkgSt := by
    with_unfolding_all exact isPkgInit_access (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.replica.defs
  refine ⟨?_, ?_⟩
  · refine hsw.trans ?_
    iintro #Hst
    ihave ⟨-, -, #Hr⟩ := swift.pkgSt_hooks $$ Hst
    ihave #Hp := swift.pkgSt_poolOff _ hnr $$ [$Hst]
    · ipureintro; rfl
    ihave ⟨%ov, #Hov, %Hne⟩ := swift.pkgSt_errVarint $$ Hst
    iframe Hr Hp
    iexists ov
    iframe Hov
    ipureintro; exact Hne
  · refine hdf.trans ?_
    unfold defs.pkgSt
    exact .rfl

variable [G : GooseGlobalGS .hasLC netDistGF]

/-- **The client nodes' callees**, linked: the test package's initialization (the packages'
initializers, ClientPkgInits.lean), `registerRPC`, the client package's specs (group E,
Proof/client/Link.lean), the swift client's `NewClient`, L2's claim and the client node's taking
of its fresh ghost (ClaimLink.lean). -/
theorem client_node_hyps : cnode.ClientNodeHyps pkgStates := by
  intro hG s hGG _ _ _ c ip hc hip hnet
  have hnr : ¬ swift.replicaNode (netIp (L := hG.goose_localGS) (GF := netDistGF)) := by
    rw [hnet]; exact (clientIp_key c ip hc hip).2
  have facts := client_pkg_facts hG s hnr
  have hfresh := client_fresh hG s c ip hc hip hnet
  letI := @pkgStates _ netDistGF hG s
  subst hGG
  exact {
    init := fun g hg => adapter.initialize.wp_proof adapter.swiftInits g hg
    reg := registerRPC.wp_proof net.rpc.SetCodec.wp_proof (encoding.gob.SetCodec.wp_proof rfl)
    ncl := client.wp_NewClientLog
    nbc := client.wp_NewBufferClient
    conn := client.BufferClient.wp_ConnectG facts
    disc := client.BufferClient.wp_DisconnectG
    write := client.BufferClient.wp_Write dlog.Logger.wp_Println
    read := client.BufferClient.wp_Read dlog.Logger.wp_Println
    nc := swift.wp_NewClient facts
    claim := client.claimGhost.wp_proof
    fresh := hfresh }

end link

section parts
variable [GoGlobalContext] [GooseGlobalGS .hasLC netDistGF]

/-- The start (Proof/swiftnet/Start.lean). -/
theorem start_ok : StartOk := start_ok'

/-- The client nodes (Proof/swiftnet/ClientNodeLink.lean, over `client_node_hyps`). -/
def client_node_ok_linked : ClientNodeOk pkgStates := client_node_ok client_node_hyps

/-- The server nodes (Proof/swiftnet/ServersLink.lean, over L2's claim, ClaimLink.lean). -/
theorem servers_ok_full : ServersOk := servers_ok claim_hyp

end parts

/-- **`goal_spec`'s statement**, from its parts (`goal_spec_of`, Spec/swiftnet/Interface.lean). -/
theorem goal_spec_parts [GoGlobalContext] : SwiftNetSpecHolds :=
  goal_spec_of pkgStates (fun {_} => start_ok) (fun {_} => orch_ok)
    (fun {_} => client_node_ok_linked) (fun {_} => servers_ok_full)

end Perennial.github_com.imdea_software.swiftpaxos
