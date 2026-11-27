/-
The proof of `Net/Spec/net/UDPConn__ReadFromUDP.lean`: Go's `ReadFromUDP` and `readFromUDP` (`ok()`,
the `*OpError` of a failure), over the model's `UDPConn.readFrom` (`wp_readFrom`: the UDP extension's
`Recv` takes the caller's update; the bytes are then copied into the buffer).
-/
module

public import Net.Spec.net.UDPConn__ReadFromUDP
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

theorem UDPConn.ReadFromUDP.wp_proof : UDPConn.ReadFromUDP.spec (GF := GF) (hG := hG) := by
  intro c s a b bs0 Q
  wp_start as ⟨#Hc, Hb, HAU⟩
  ihave ⟨%fd, %la, %v, #Hcp, #Hv, %hv, #Hla⟩ := udpConnAt_elim _ _ _ $$ Hc
  obtain ⟨-, hnet, -, hra⟩ := hv
  ihave %Hfdn := typedPointsto_not_null _ _ _ $$ Hv
  ihave #Hcp2 := Hcp
  iStructNamed Hcp2
  iStructNamed conn
  ihave #Hv2 := Hv
  iStructNamed Hv2
  (try wp_method_call)
  (try wp_call)
  wp_auto
  wp_method_call; wp_call
  wp_auto
  wp_apply wp_UDPConn_ok c fd Hfdn $$ Hcp
  (try wp_auto)
  wp_apply wp_readFrom c s a b bs0 _ _ Q $$ Hc Hb [$] HAU
  iintro %od %n %ra %e HQ Hod
  cases od with
  | none =>
    dsimp only
    icases Hod with ⟨%hn, Hb, -, #He⟩
    obtain ⟨rfl, rfl⟩ := hn
    ihave #He2 := He
    iunfold sysErr at He2
    icases He2 with ⟨%pe, %nm, %k, %h, -⟩
    obtain ⟨rfl, -, -⟩ := h
    iapply wp_fupd
    wp_auto
    wp_alloc po as Hpo
    wp_auto
    ipersist Hpo
    imodintro
    iapply HΦ
    iexists none
    dsimp only
    iframe HQ Hb
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iexists v.laddr'
    unfold udpErr
    iexists po, _
    isplitr
    · ipureintro; rfl
    rw [← hnet, ← hra]
    iframe Hpo He
  | some d =>
    dsimp only
    icases Hod with ⟨%hn, Hb, -⟩
    obtain ⟨hn, rfl, rfl⟩ := hn
    wp_auto
    iapply HΦ
    iexists some d
    dsimp only
    iframe HQ Hb
    ipureintro
    exact ⟨hn, rfl⟩

end proof

end net
end Perennial
