/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/ClientCallees.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Proofs of the client listener's small callees (`Proof/replica/ClientSpecs.lean`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.replica.ClientSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions] [config.Assumptions]

set_option goose.wp.extras true

theorem replica.defs.LatencyTable.WaitDuration.wp_proof :
    replica.defs.LatencyTable.WaitDuration.spec (hG := hG) := by
  intro addr
  wp_start
  wp_auto
  iapply HΦ; itrivial

theorem replica.defs.NewDelayProposeChan.wp_proof :
    replica.defs.NewDelayProposeChan.spec (hG := hG) := by
  intro c
  wp_start
  wp_auto
  iapply HΦ
  iexists _
  iframe «$r0»
  ipureintro; exact ⟨rfl, rfl⟩

theorem replica.defs.DelayProposeChan.Write.wp_proof :
    replica.defs.DelayProposeChan.Write.spec (hG := hG) := by
  intro dc c γch P p
  wp_start as ⟨#Hdc, #Hbag, HP⟩
  iunfold replica.defs.dpcOk at Hdc
  icases Hdc with ⟨%v, #Hv, %Hvp⟩
  iStructNamed Hv
  obtain ⟨h0, rfl⟩ := Hvp
  wp_auto
  rw [h0]
  simp only [decide_true]
  wp_auto
  wp_apply (wp_bag_send (V := Loc) γch v.pChan' p P) $$ [HP]
  · iframe HP; iexact Hbag
  iapply HΦ; itrivial

theorem config.ProxyInfo.IsProxy.wp_proof : config.ProxyInfo.IsProxy.spec (hG := hG) := by
  intro pp pi al addr
  wp_start as ⟨#Hpi, %Hnil⟩
  iStructNamed Hpi
  wp_auto
  rw [Hnil, show (null : Loc) = map.nil from rfl]
  wp_auto
  iapply HΦ; itrivial

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
