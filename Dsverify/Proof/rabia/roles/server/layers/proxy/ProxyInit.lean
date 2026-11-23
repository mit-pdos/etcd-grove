/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/proxy/ProxyInit.lean`, run `rabia-r1wake-1`.)

`ProxyInit`: the logger (G4: none), the endpoint (`ProxyTcpInit`), the empty store, no Redis client
(`StorageMode` 0), and the function fields set to the in-memory store's (`naiveExecuteCmd`,
`singleExecuteAndReply`).
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.proxy.Basics
public import Dsverify.Proof.rabia.internal.logger.InitLogger
public import Dsverify.Proof.rabia.internal.tcp.Spec
public import Perennial.Proof.context

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

/-- `RedisInit(id)` with the in-memory store (`StorageMode` 0): `nil`. -/
theorem wp_RedisInit (cf : RCfg) (id : w32) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.roles.server.layers.proxy ∗ confRO cf }}
    (App (Val (@! RedisInit)) (Val #id))
  {{ RET #(null : Loc); True }} := by
  wp_start as #Hconf
  icases confRO_val $$ Hconf with ⟨%ps, #Hc⟩
  iStructNamed Hc
  wp_auto
  iapply HΦ
  itrivial

theorem ProxyInit.wp_of (hLog : rabia.internal.logger.InitLogger.spec (GF := GF))
    (hTcp : ProxyTcpInit.spec (GF := GF)) : ProxyInit.spec (GF := GF) := by
  intro γ cf k γl γc ch id wg ledger hid hk
  wp_start as ⟨#Hconf, #Hchans, #Hled, #Hslots, Haddr, Hboot⟩
  icases confRO_val $$ Hconf with ⟨%ps, #Hc⟩
  iStructNamed Hc
  unfold proxyBootRes
  icases Hboot with ⟨Hkp, #Hkeys, Hcr, Hrc⟩
  ihave #Hbc2p : iprop(isChanBag γl.c2p ch.c2p (c2pP γ cf k γl)) $$ []
  · unfold srvChans
    icases Hchans with ⟨-, #Hbc2p, -⟩
    iexact Hbc2p
  wp_auto
  wp_apply hLog cf $$ [$Hconf] as %lg -
  wp_apply hTcp γ cf k γl id ch.c2p hid hk $$ [$Hconf $Haddr $Hbc2p $Hrc] as %t ⟨#Htcp, Htown⟩
  wp_apply wp_map_make1 (K := GoString) (V := GoString) as %kv Hkv
  wp_apply wp_RedisInit cf $$ [$Hconf]
  wp_apply +noauto context.wp_Background
  iapply wp_fupd
  wp_auto
  irename «$r0» => Hp
  iStructNamed Hp
  ipersist SvrId
  ipersist Wg
  ipersist Done
  ipersist ClientsIn
  ipersist ToNet
  ipersist NetIn
  ipersist TCP
  ipersist KVStore
  ipersist executeCmdFunc
  ipersist executeAndReplyFunc
  ipersist Ledger
  imodintro
  iapply HΦ
  isplitl
  · unfold proxyInitOk
    iexists wg, t, kv, ledger, null
    isplitr
    · ipureintro; exact hk
    isplitr
    · unfold proxyFields
      iexists id
      iframe SvrId Wg Done ClientsIn ToNet NetIn TCP KVStore executeCmdFunc executeAndReplyFunc Ledger
      ipureintro; exact hid
    isplitl [CurrSeq]
    · first
        | (rw [show (W32 0 : w32) = zeroValDef from rfl]; iexact CurrSeq)
        | (rw [show (W32 0 : w32) = Perennial.zero_val w32 from rfl]; iexact CurrSeq)
        | (rw [show (W32 0 : w32) = (0 : w32) from rfl]; iexact CurrSeq)
    isplitl [CurrDec]
    · iexact CurrDec
    isplitl [Hkv]
    · iexact Hkv
    iframe Htcp Htown Hchans Hled Hslots Hkeys
    isplitl [Hkp]
    · iexact Hkp
    iexact Hcr
  · unfold proxyRO
    iexists t
    iframe TCP Htcp

/-- `ProxyInit.spec`: from tcp's `ProxyTcpInit` spec (an argument, linked by the kit). -/
theorem ProxyInit.wp_proof [github_com.rs.zerolog.Hyps GF] (hTcp : ProxyTcpInit.spec (GF := GF)) : ProxyInit.spec (GF := GF) :=
  ProxyInit.wp_of rabia.internal.logger.InitLogger.wp_proof hTcp

end proof
end Perennial.rabia.roles.server.layers.proxy
