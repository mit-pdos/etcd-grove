-- The copy for the part `KvRaft/` of `Net/Proof/net/UDPConn__WriteToUDP.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The proof of `Net/Spec/net/UDPConn__WriteToUDP.lean`: Go's `WriteToUDP` (`ok()`, the `*OpError` of
a failure), over the model's `UDPConn.writeTo` (`wp_writeTo`: the UDP extension's `Send` takes the
caller's update).
-/
module

public import KvRaft.Spec.net.UDPConn__WriteToUDP
public import KvRaft.Proof.net.UdpModels

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

theorem UDPConn.WriteToUDP.wp_proof : UDPConn.WriteToUDP.spec (GF := GF) (hG := hG) := by
  intro c s la b q bs p ip port a Q
  wp_start as ⟨#Hc, Hb, #Hp, %Hv, HAU⟩
  ihave ⟨%fd, %lad, %v, #Hcp, #Hv, %hv, #Hla⟩ := udpConnAt_elim _ _ _ $$ Hc
  obtain ⟨-, hnet, -, -⟩ := hv
  ihave %Hfdn := typedPointsto_not_null _ _ _ $$ Hv
  ihave %Hnn : ⌜p ≠ null⌝ $$ [Hp]
  · unfold udpAddrAt
    icases Hp with ⟨%sl, %z, #Hpt, -⟩
    iapply typedPointsto_not_null _ _ _ $$ Hpt
  ihave #Hcp2 := Hcp
  iStructNamed Hcp2
  iStructNamed conn
  ihave #Hv2 := Hv
  iStructNamed Hv2
  (try wp_method_call)
  (try wp_call)
  wp_auto
  wp_apply wp_UDPConn_ok c fd Hfdn $$ Hcp
  (try wp_auto)
  wp_apply wp_writeTo c s la b q bs p ip port a Q $$ Hc Hb Hp %Hv HAU
  iintro %r %n %e Hb HQ Hres
  icases Hres with (⟨%hr, %hn, %he⟩ | ⟨⟨%hr, %hn⟩, #He⟩)
  · subst hn he
    wp_auto
    iapply HΦ
    iframe Hb
    iexists _
    iframe HQ
    ileft
    ipureintro
    exact ⟨by simp [hr], rfl, rfl⟩
  · subst hn
    ihave #He2 := He
    iunfold sysErr at He2
    icases He2 with ⟨%pe, %nm, %k, %h, -⟩
    obtain ⟨rfl, -, -⟩ := h
    iapply wp_fupd
    wp_auto
    wp_apply wp_UDPAddr_opAddr p Hnn
    (try wp_auto)
    wp_alloc po as Hpo
    wp_auto
    ipersist Hpo
    imodintro
    iapply HΦ
    iframe Hb
    iexists _
    iframe HQ
    iright
    isplitr
    · ipureintro; exact ⟨by simp [hr], rfl⟩
    iexists v.laddr'
    unfold udpErr
    iexists po, _
    isplitr
    · ipureintro; rfl
    rw [← hnet]
    iframe Hpo He

end proof

end net
end Perennial
