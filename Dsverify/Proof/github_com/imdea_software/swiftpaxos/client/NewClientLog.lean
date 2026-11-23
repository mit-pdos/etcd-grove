/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/NewClientLog.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
module

public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.NewClientLog
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

-- PORT: lab imports dropped: Harness.Proof.uuid.Specs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
  [SwiftOsRandom netDistGF]
variable [client.Assumptions] [github_com.google.uuid.Assumptions]

theorem client.NewClientLog.wp_proof : client.NewClientLog.spec (hG := hG) := by
  intro server maddr mport verbose lg
  wp_start as #Hq
  ihave #Hq' := Hq
  iunfold dlog.quiet at Hq'
  icases Hq' with ⟨%Hlg, -⟩
  wp_auto
  rw [decide_eq_false Hlg]
  wp_auto
  wp_apply github_com.google.uuid.wp_New as %u -
  wp_apply github_com.google.uuid.wp_ID as %x -
  iapply HΦ
  iexists _
  iapply (client.fresh_unfold _ _ _ _).2
  iexists _
  iframe
  isplitr
  · iexact Hq
  ipureintro
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end proof

end Perennial.github_com.imdea_software.swiftpaxos
