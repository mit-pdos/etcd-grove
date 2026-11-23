/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/Server__ServerMain.lean`, run `rabia-r1wake-1`.)

The proof of `rabia/roles/server.(*Server).ServerMain`: three `Wg.Add(2)` (the counter, nobody
waits), the six routines forked, then the receive on `Done` (a bag of `False`: never returns).
-/
module

public import Dsverify.Proof.rabia.internal.queue.Spec
public import Dsverify.Proof.rabia.roles.server.layers.proxy.Spec
public import Dsverify.Proof.rabia.roles.server.layers.network.Spec
public import Dsverify.Proof.rabia.roles.server.Spec
public import Perennial.Proof.sync.Link
public import Dsverify.Proof.rabia.roles.server.layers.consensus.Spec
public import Dsverify.Proof.rabia.internal.ledger.Spec

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

/-- `wg.Add(2)` with the counter and no waiter. -/
theorem wp_wg_add2 (wg : Loc) (γw : sync.WaitGroupNames) (N : Namespace) (c : w32)
    (hc : 0 ≤ sint.Z c ∧ sint.Z c + 2 < 2 ^ 31) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isWaitGroup wg γw N ∗
        sync.ownWaitGroup γw c ∗ sync.ownWaitGroupWaiters γw 0 }}
      (App (Val (wg @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Add")) (Val #(W64 2)))
    {{ RET #(); sync.ownWaitGroup γw (c + W32 2) ∗ sync.ownWaitGroupWaiters γw 0 }} := by
  iintro %Φ ⟨#Hpkg, #Hwg, Hc, Hw⟩ HΦ
  iapply sync.WaitGroup.wp_Add wg (W64 2) γw N $$ [] [Hc Hw HΦ]
  · isplitr
    · iexact Hpkg
    · iexact Hwg
  iapply fupd_mask_intro (show (↑N : CoPset) ⊆ ⊤ from CoPset.subseteq_top)
  iintro Hmask
  inext
  iexists c
  iframe Hc
  isplitr
  · ipureintro
    have : sint.Z (W32 (sint.Z (W64 2))) = 2 := by decide
    rw [this]; omega
  iright
  iframe Hw
  iintro Hw Hc
  imod Hmask with -
  imodintro
  iapply HΦ
  have : W32 (sint.Z (W64 2)) = W32 2 := by decide
  rw [this]
  iframe

theorem Server.ServerMain.wp_proof (hCR : Proxy.CmdReceiver.spec (GF := GF))
    (hKE : Proxy.KVSExecutor.spec (GF := GF)) (hMR : Network.MsgRouter.spec (GF := GF))
    (hMS : Network.MsgSerializer.spec (GF := GF)) (hEx : Consensus.Executor.spec (GF := GF))
    (hMH : Consensus.MsgHandler.spec (GF := GF)) : Server.ServerMain.spec (GF := GF) := by
  intro γ cf k s
  wp_start as ⟨#Hconf, #Hsh, #Hcfg, Hr⟩
  unfold serverReady
  icases Hr with ⟨%γl, %γc, %ch, %p, %n, %c, Hro, Hown, #Hchans, Hcr, Hkr, Hrr, Hsr, Hexr, Hhar⟩
  unfold serverRO serverOwn
  icases Hro with ⟨#HId, #HDone, #HProxy, #HNet, #HCons⟩
  icases Hown with ⟨%wg, %γw, #HWg, #Hwg, Hc, Hw⟩
  wp_auto
  wp_apply wp_wg_add2 wg γw (srvWgN k) (W32 0) (by decide) $$ [$Hwg $Hc $Hw] as ⟨Hc, Hw⟩
  wp_apply wp_fork $$ [Hcr]
  · wp_apply hCR γ cf k γl ch p $$ [Hcr] as Hf
    · iframe #; iexact Hcr
    iexfalso; iexact Hf
  wp_apply wp_fork $$ [Hkr]
  · wp_apply hKE γ cf k γl γc p $$ [Hkr] as Hf
    · iframe #; iexact Hkr
    iexfalso; iexact Hf
  wp_apply wp_wg_add2 wg γw (srvWgN k) (W32 0 + W32 2) (by decide) $$ [$Hwg $Hc $Hw] as ⟨Hc, Hw⟩
  wp_apply wp_fork $$ [Hrr]
  · wp_apply hMR γ cf k γl ch n $$ [Hrr] as Hf
    · iframe #; iexact Hrr
    iexfalso; iexact Hf
  wp_apply wp_fork $$ [Hsr]
  · wp_apply hMS γ cf k γl n $$ [Hsr] as Hf
    · iframe #; iexact Hsr
    iexfalso; iexact Hf
  wp_apply wp_wg_add2 wg γw (srvWgN k) (W32 0 + W32 2 + W32 2) (by decide) $$ [$Hwg $Hc $Hw]
    as ⟨Hc, Hw⟩
  wp_apply wp_fork $$ [Hexr]
  · wp_apply hEx γ cf k γl γc ch c $$ [Hexr] as Hf
    · iframe #; iexact Hexr
    iexfalso; iexact Hf
  wp_apply wp_fork $$ [Hhar]
  · wp_apply hMH γ cf k γl γc ch c $$ [Hhar] as Hf
    · iframe #; iexact Hhar
    iexfalso; iexact Hf
  ihave #Hc2 := Hchans
  unfold srvChans
  icases Hc2 with ⟨#Hd, -⟩
  wp_apply (wp_bag_receive (V := Unit) γl.done ch.done doneP) $$ [$Hd] as %v Hf
  unfold doneP
  iexfalso; iexact Hf

end proof
end Perennial.rabia.roles.server
