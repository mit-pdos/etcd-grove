/-
The proof of `Net/Spec/net/ListenUDP.lean`: Go's `ListenUDP` (the network's switch, `laddr.String()`,
`context.Background()`, the `*OpError` of a failure), over the model's `sysListener.listenUDP`
(`wp_listenUDP`: the UDP extension's `Listen`, then a new `*UDPConn` over a datagram `netFD`).
-/
module

public import Net.Spec.net.ListenUDP
public import Net.Proof.net.UdpModels

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Udp

namespace net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt udpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions]
variable [go.BasicIntoValInj]

theorem ListenUDP.wp_proof : ListenUDP.spec (GF := GF) (hG := hG) := by
  intro p ip port a
  wp_start as ⟨#Hp, %Hv⟩
  ihave %Hnn : ⌜p ≠ null⌝ $$ [Hp]
  · unfold udpAddrAt
    icases Hp with ⟨%sl, %z, #Hpt, -⟩
    iapply typedPointsto_not_null _ _ _ $$ Hpt
  wp_auto
  (try rw [decide_eq_false Hnn])
  (try simp only [Hnn, ↓reduceIte, decide_false, Bool.false_eq_true])
  (try wp_auto)
  wp_apply wp_UDPAddr_String p as %str
  (try wp_auto)
  -- `context.Background()` (`backgroundCtx{}`)
  wp_func_call; wp_call
  wp_auto
  wp_apply wp_listenUDP _ _ _ _ p ip port a $$ [$] Hp %Hv
  isplit
  · -- a new socket
    iintro %c #Hc
    wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexact Hc
  · -- a failure
    iintro %e #He
    ihave %hok : ⌜∃ i, e = GoInterface.ok i⌝ $$ [He]
    · icases He with (#He | %He)
      · iunfold sysErr at He
        icases He with ⟨%pe, %nm, %k, %h, -⟩
        ipureintro; rw [h.1]; exact ⟨_, rfl⟩
      · ipureintro; obtain ⟨n, -, rfl⟩ := He; exact ⟨_, rfl⟩
    obtain ⟨i, rfl⟩ := hok
    iapply wp_fupd
    wp_auto
    wp_apply wp_UDPAddr_opAddr p Hnn
    (try wp_auto)
    wp_alloc po as Hpo
    wp_auto
    ipersist Hpo
    imodintro
    iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    unfold udpListenErr
    iexists po, _
    isplitr
    · ipureintro; rfl
    iframe Hpo He

end proof

end net
end Perennial
