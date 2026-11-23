/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/BatcherFast.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The batcher's fast-ack senders (round 14; `handlePropose`'s fast ack): `b.SendFastAck(l)` and
`b.SendFastAckClient(l, cid)` (batcher.go) put an operation with `batchFastP` on the batcher's
fast-ack channel.

* `swift.fastOpP γ γc γm rp l cl`: `batchFastP` but the operation: the sending context, the
  owned `*MFastAck` (freed by the batcher), its model ack sent by this replica with its witness,
  well formed and not shaped as a slow ack, and for a client copy (`cl`) `facClientOk`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.NewSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.BatcherFastDefs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section specs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

end specs

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions]

theorem swift.Batcher.SendFastAck.wp_proof : swift.Batcher.SendFastAck.specI (hG := hG) := by
  intro γ γc γm rp b l
  wp_start as ⟨#Hb, Hop⟩
  iunfold swift.batcherH at Hb
  icases Hb with ⟨%fa, %ls, %γ1, %γ2, #Hbs, #Hfa, #Hls⟩
  ihave #Hbs2 := Hbs
  iStructNamedPrefix Hbs2 "B"
  wp_auto
  wp_apply wp_bag_send (t := swift.BatcherOp.ty) γ1 fa _ (swift.batchFastP γ γc γm rp) $$ [Hop]
  · iframe Hfa
    iunfold swift.fastOpP at Hop
    icases Hop with ⟨%N, %me, %fa', %f, #Hc, Hl, #Hr, #Hok, %Hf, Hcl⟩
    iunfold swift.batchFastP
    iexists N, me, l, fa', f
    iframe Hc Hl Hr Hok
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact Hf
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
  iapply HΦ; itrivial

theorem swift.Batcher.SendFastAckClient.wp_proof :
    swift.Batcher.SendFastAckClient.specI (hG := hG) := by
  intro γ γc γm rp b l cid
  wp_start as ⟨#Hb, Hop⟩
  iunfold swift.batcherH at Hb
  icases Hb with ⟨%fa, %ls, %γ1, %γ2, #Hbs, #Hfa, #Hls⟩
  ihave #Hbs2 := Hbs
  iStructNamedPrefix Hbs2 "B"
  wp_auto
  wp_apply wp_bag_send (t := swift.BatcherOp.ty) γ1 fa _ (swift.batchFastP γ γc γm rp) $$ [Hop]
  · iframe Hfa
    iunfold swift.fastOpP at Hop
    icases Hop with ⟨%N, %me, %fa', %f, #Hc, Hl, #Hr, #Hok, %Hf, Hcl⟩
    iunfold swift.batchFastP
    iexists N, me, l, fa', f
    iframe Hc Hl Hr Hok
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; exact Hf
    iexact Hcl
  iapply HΦ; itrivial

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
