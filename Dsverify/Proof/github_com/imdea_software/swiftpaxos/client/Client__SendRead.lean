/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/Client__SendRead.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.ISpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Marshal

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [client.Assumptions] [state.Assumptions]

theorem client.Client.SendRead.wp_proof
    (wp_SendProposal : client.Client.SendProposal.specI (hG := hG)) :
    client.Client.SendRead.specI (hG := hG) := by
  intro cl γ γc γm cid N s key
  wp_start as ⟨Hseq, Hsend, #Hcmd⟩
  iunfold client.sendSt at Hsend
  icases Hsend with ⟨%lg, %ld, %ssl, %wsl, %wrs, #Hcid, Hrest⟩
  wp_auto
  wp_apply wp_NIL as %vsl Hv
  ipersist Hv
  have hs1 : W32 ((s : Int) - 1) + W32 1 = W32 (s : Int) := by word
  rw [hs1]
  wp_apply wp_SendProposal cl γ γc γm cid N _ (W32 (s : Int)) (sp.Cmd.get key)
    $$ [Hrest] as Hsend
  · isplitl [Hrest]
    · unfold client.sendSt; iexists lg, ld, ssl, wsl, wrs; iframe; iframe #
    isplitr
    · simp only [sp.Cmd.get]; iexact Hv
    iframe #
    ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, by simp [sp.Cmd.get]⟩
  iapply HΦ
  iframe

end proof

end Perennial.github_com.imdea_software.swiftpaxos
