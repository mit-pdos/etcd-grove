/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/proxy/Prologue.lean`, run `rabia-r1wake-1`.)

`(*Proxy).Prologue`: the endpoint's `Connect` (accepting in the background); the routines'
resources are split from `proxyInitOk`.
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.proxy.Basics
public import Dsverify.Proof.rabia.internal.tcp.Spec

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.proxy

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.tcp rabia.roles.server.layers.consensus rabia

set_option linter.unusedSectionVars false

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.roles.server.layers.proxy.Assumptions]

theorem Proxy.Prologue.wp_proof (hConn : ProxyTCP.Connect.spec (GF := GF)) :
    Proxy.Prologue.spec (GF := GF) := by
  intro γ cf k γl γc ch p
  wp_start as ⟨#Hconf, #Hsh, #Hcfg, Hres⟩
  unfold proxyInitOk
  icases Hres with ⟨%wg, %t, %kv, %ledger, %cd, %hk, #Hf, Hseq, Hcd, Hkv, #Htcp, Htown, #Hchans,
    #Hled, #Hslots, #Hkeys, Hkp, Hcr⟩
  ihave #HTCP : iprop(structFieldRef Proxy go!"TCP" p ↦□ t) $$ []
  · unfold proxyFields
    icases Hf with ⟨%id, %hid, -, -, -, -, -, -, #HTCP, -⟩
    iexact HTCP
  wp_auto
  wp_apply hConn γ cf k γl t $$ [$Hconf $Hsh $Hcfg $Htcp $Htown]
  iapply HΦ
  isplitl [Hkp Hcr]
  · unfold proxyCmdRes
    iexists wg, t, kv, ledger
    iframe Hf Hchans Hkeys
    isplitr
    · ipureintro; exact hk
    isplitl [Hkp]
    · iexact Hkp
    iexact Hcr
  · unfold proxyKvsRes
    iexists ch, wg, t, kv, ledger, cd
    iframe Hf Hseq Hcd Hkv Hled Hslots Htcp
    unfold srvChans
    icases Hchans with ⟨#Hd, -⟩
    iexact Hd

end proof
end Perennial.rabia.roles.server.layers.proxy
