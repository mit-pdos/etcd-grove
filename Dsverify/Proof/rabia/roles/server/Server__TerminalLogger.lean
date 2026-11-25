/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/Server__TerminalLogger.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/roles/server.(*Server).TerminalLogger`: a logger (G4: it writes nothing),
the deferred sync of its file (`nil`: never runs, the loop does not end), a ticker, and the loop
on `Done` (a bag of `False`) and the ticker's channel: each tick reads the proxy's number of
connections and the slots' statistics and logs them.
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.consensus.Spec
public import Dsverify.Proof.rabia.roles.server.Spec
public import Dsverify.Proof.github_com.rs.zerolog.Spec
public import Dsverify.Proof.rabia.internal.logger.Spec
public import Perennial.Proof.time.Link
public import Dsverify.Proof.rabia.internal.tcp.Spec

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.roles.server.layers.network rabia.roles.server.layers.consensus
  rabia.roles.server.layers.proxy rabia rabia.internal.tcp

set_option linter.unusedSectionVars false

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.roles.server.Assumptions] [github_com.rs.zerolog.Hyps GF]

theorem confRO_elim' (cf : RCfg) : (confRO cf : IProp GF) ⊢
    ∃ ps, (globalAddr Conf ↦□ confVal cf ps : IProp GF) ∗ ps ↦*□ peerStrs cf := by
  unfold confRO; iintro ⟨-, H⟩; iexact H

theorem Server.TerminalLogger.wp_proof
    (hIL : rabia.internal.logger.InitLogger.spec (GF := GF))
    (hNC : ProxyTCP.NumConns.spec (GF := GF)) (hSS : Consensus.SlotStats.spec (GF := GF)) :
    Server.TerminalLogger.spec (GF := GF) := by
  have hE := github_com.rs.zerolog.eventSpecs (GF := GF)
  have hW := hE.level go!"Warn" (by simp)
  have hU := hE.Event_Uint32
  have hI := hE.Event_Int
  have hFl := hE.Event_Float64
  have hM := hE.Event_Msg
  intro γ cf k s
  wp_start as ⟨#Hconf, Hr⟩
  unfold serverLogRes
  icases Hr with ⟨%γl, %ch, %p, %n, %c, Hro, #Hchans, Hpro, #Hstro⟩
  unfold serverRO proxyRO
  icases Hro with ⟨#HId, #HDone, #HProxy, #HNet, #HCons⟩
  icases Hpro with ⟨%t, #HTCP, #Htro⟩
  ihave ⟨%cps, #Hc, #Hcps⟩ := confRO_elim' cf $$ Hconf
  ihave Hc2 := Hc
  iStructNamedPrefix Hc2 "C"
  wp_apply wp_with_defer as %defer Hdefer
  wp_apply hIL cf $$ [] as %lg #Hlok
  · iexact Hconf
  wp_apply time.wp_NewTicker (W64 4000000000) as %tk %tch %γt #Htk
  · ipureintro; decide
  unfold time.isTicker
  icases Htk with ⟨#HC, -, -, #Htbag⟩
  ihave HI : (∃ (a b : w64), "lastNotNulls" ∷ lastNotNulls_ptr ↦ a ∗
      "lastCBProcessed" ∷ lastCBProcessed_ptr ↦ b) $$ [lastNotNulls lastCBProcessed]
  · iexists W64 0, W64 0; iframe
  wp_for_core
  iNamed HI
  wp_call_lc Hlc0
  simp only [decide_true, ↓reduceIte]
  wp_auto_lc 1
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · dsimp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch.done, γl.done
    isplitr
    · ipureintro; rfl
    ihave #Hc3 := Hchans
    unfold srvChans
    icases Hc3 with ⟨#Hd, -⟩
    ihave #Hdc := is_bag_is_chan _ _ _ $$ Hd
    iframe Hdc
    iapply bag_recv_au $$ [$Hlc0 $Hlc1] Hd
    inext
    iintro %v Hf
    unfold doneP
    iexfalso; iexact Hf
  iapply BigAndL.bigAndL_cons.2
  isplit
  · dsimp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
    isplitr
    · ipureintro; rfl
    ihave #Htc := is_bag_is_chan _ _ _ $$ Htbag
    iframe Htc
    iapply bag_recv_au $$ [$Hlc0 $Hlc1] Htbag
    inext
    iintro %v -
    wp_auto
    wp_apply hNC γ k t $$ [] as %nconn -
    · iexact Htro
    wp_apply hSS c $$ [] as %a1 %a2 %a3 %a4 -
    · iexact Hstro
    wp_apply hW tLogger_ptr lg (DFrac.own 1) $$ [$tLogger $Hlok] as %e ⟨tLogger, He⟩
    wp_apply hU $$ [$He] as He
    wp_apply hI $$ [$He] as He
    wp_apply hI $$ [$He] as He
    wp_apply hI $$ [$He] as He
    wp_apply hI $$ [$He] as He
    wp_apply hI $$ [$He] as He
    wp_apply hFl $$ [$He] as He
    wp_apply hM $$ [$He]
    wp_for_post
    iframe
    iexists _, _
    iframe
  · iapply BigAndL.bigAndL_nil.2
    itrivial

end proof
end Perennial.rabia.roles.server
