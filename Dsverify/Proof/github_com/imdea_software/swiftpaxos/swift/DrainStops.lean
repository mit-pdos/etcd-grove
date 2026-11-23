/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/DrainStops.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
Copyright (c) 2026. All rights reserved.

**`r.drainStops(desc)`** (round 42; table §3R11 T17, T19d; plan R11.4 (4) 2): every stop request
still queued on the descriptor's `stopChan` is answered. Each request carries the incarnation's
signal token `sgTok γsg` and half of the round's element of the key `k`; the caller holds the token
(unsignalled) or the element's other half (signalled). A request met with the token in hand is
refuted (two tokens); met with the half in hand, the two halves make `Done`'s `P`, and the request's
token is kept for the next one.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SlotSpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.DrainStopsDefs

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF] [SwiftKitDeps]
variable [swift.Assumptions] [replica.Assumptions] [replica.defs.Assumptions] [rpc.Assumptions]
variable [sync.Assumptions]

theorem swift.Replica.drainStops.wp_proof : swift.Replica.drainStops.specT := by
  intro rp d sc γsc γs γsg k qc
  wp_start as ⟨Hsc, #Hbag, Htok⟩
  iunfold swift.stopBag at Hbag
  icases Hbag with ⟨%W, #Hb, #HW⟩
  ihave #Hch := is_bag_is_chan γsc sc _ $$ Hb
  wp_auto
  ihave HL : (∃ _u : Unit, "Hsc" ∷ typedPointsto (swift.dfld d go!"stopChan") sc (DFrac.own qc) ∗
      "Htok" ∷ (swift.sgTok γsg ∨ ghostMapElem γs k (DFrac.own (1 : Qp).half) true) : IProp netDistGF)
    $$ [Hsc Htok]
  · iexists (); iframe
  wp_for HL
  wp_func_call
  wp_call
  wp_apply (wp_Len (V := Loc) (t := go.GoType.PointerType sync.WaitGroup.ty) sc γsc) $$ [$Hch] as %l %Hl
  wp_if_destruct
  · wp_apply (wp_bag_receive (t := go.GoType.PointerType sync.WaitGroup.ty) γsc sc _) $$ [$Hb] as %wg ⟨Hm, -⟩
    ihave ⟨Hd, Hk, Htok2⟩ := swift.drainStops_step γs γsg k d sc wg $$ [Hm Htok]
    · iframe
    try wp_auto
    wp_apply (sync.join.WaitGroup.wp_Done (ghostMapElem γs k (DFrac.own 1) true) wg) $$ [Hd Hk]
    · iframe
    try wp_auto
    wp_for_post
    iframe
    iexists ()
    iframe Hsc
    ileft; iexact Htok2
  · rw [if_pos (by cases hd : decide (l = W64 0) <;> simp_all)]
    try wp_auto
    iapply HΦ
    iframe Hsc

end proofs

end Perennial.github_com.imdea_software.swiftpaxos
