/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/Server__Prologue.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/roles/server.(*Server).Prologue`.
-/
module

public import Dsverify.Proof.rabia.roles.server.Server__TerminalLogger
public import Dsverify.Proof.rabia.internal.system.SigListen
public import Dsverify.Proof.rabia.roles.server.layers.proxy.Spec
public import Dsverify.Proof.rabia.roles.server.layers.network.Spec
public import Dsverify.Proof.rabia.roles.server.layers.proxy.Prologue
public import Dsverify.Proof.rabia.roles.server.layers.network.Prologue

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.roles.server.layers.network rabia.roles.server.layers.consensus
  rabia.roles.server.layers.proxy rabia

set_option linter.unusedSectionVars false

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.roles.server.Assumptions]

theorem Server.Prologue.wp_of (hSig : rabia.internal.system.SigListen.spec (GF := GF))
    (hNP : Network.Prologue.spec (GF := GF)) (hPP : Proxy.Prologue.spec (GF := GF))
    (hTL : Server.TerminalLogger.spec (GF := GF)) : Server.Prologue.spec (GF := GF) := by
  intro γ cf k s
  wp_start as ⟨#Hconf, #Hsh, #Hcfg, Hb⟩
  unfold serverBuilt
  icases Hb with ⟨%γl, %γc, %ch, %p, %n, %c, %ledger, Hro, Hown, #Hchans, #Hled, #Hsinv,
    Hpok, #Hpro, Hnok, Hexr, Hhar, #Hstro⟩
  unfold serverRO
  icases Hro with ⟨#HId, #HDone, #HProxy, #HNet, #HCons⟩
  wp_auto
  wp_apply wp_fork $$ []
  · wp_apply hSig ch.done γl.done $$ [] as Hf
    · ihave #Hc2 := Hchans
      unfold srvChans doneP
      icases Hc2 with ⟨#Hd, -⟩
      iexact Hd
    iexfalso; iexact Hf
  wp_apply hNP γ cf k γl ch n $$ [Hnok] as ⟨Hrr, Hsr⟩
  · iframe #; iexact Hnok
  wp_apply hPP γ cf k γl γc ch p $$ [Hpok] as ⟨Hcr, Hkr⟩
  · iframe #; iexact Hpok
  wp_apply wp_fork $$ []
  · wp_apply hTL γ cf k s $$ [] as Hf
    · unfold serverLogRes
      isplitr; · iexact Hconf
      iexists γl, ch, p, n, c
      unfold serverRO
      iframe #
    iexfalso; iexact Hf
  iapply HΦ
  unfold serverReady
  iexists γl, γc, ch, p, n, c
  unfold serverRO
  iframe #
  iframe


/-- `Server.Prologue.spec`, from tcp's `NetTCP.Connect` and `ProxyTCP.Connect` specs (arguments,
linked by the kit); `SigListen` under the environment assumption `os.signal.NoSignals`. -/
theorem Server.Prologue.wp_proof [github_com.rs.zerolog.Hyps GF] [os.signal.NoSignals GF]
    (hNC : rabia.internal.tcp.NetTCP.Connect.spec (GF := GF))
    (hPC : rabia.internal.tcp.ProxyTCP.Connect.spec (GF := GF)) :
    Server.Prologue.spec (GF := GF) := by
  exact Server.Prologue.wp_of rabia.internal.system.SigListen.wp_proof
    (layers.network.Network.Prologue.wp_proof hNC) (layers.proxy.Proxy.Prologue.wp_of hPC)
    Server.TerminalLogger.wp_proof

end proof
end Perennial.rabia.roles.server
