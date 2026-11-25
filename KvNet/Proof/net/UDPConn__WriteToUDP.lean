-- The copy for the part `KvNet/` of `Net/Proof/net/UDPConn__WriteToUDP.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The proof of `Net/Spec/net/UDPConn__WriteToUDP.lean`: `UDPConn.WriteToUDP.impl`'s extension
`Send` takes the caller's update (`Udp.wp_udp_Send`).
-/
module

public import KvNet.Spec.net.UDPConn__WriteToUDP
public import KvNet.Proof.net.UdpModels

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
variable [package_sem' : net.Assumptions] [field_sem : net.UdpFieldAssumptions]
variable [go.BasicIntoValInj]

theorem UDPConn.WriteToUDP.wp_proof : UDPConn.WriteToUDP.spec (GF := GF) (hG := hG) := by
  intro c s la b q bs p ip port a Q
  unfold udpConnAt
  wp_start as ⟨⟨%lad, #Hc, #Hlad, %Hs0, #Hsock⟩, Hb, #Hp, %Hv, HAU⟩
  ihave %Hnn : ⌜p ≠ null⌝ $$ [Hp]
  · unfold udpAddrAt
    icases Hp with ⟨%sl, %z, #Hpt, -⟩
    iapply typedPointsto_not_null _ _ _ $$ Hpt
  (try wp_method_call)
  (try unfold UDPConn.WriteToUDP.impl)
  (try unfold model.udpId)
  rw [UDPConn_ty_eq, UDPAddr_ty_eq]
  ihave #Hc2 := Hc
  iStructNamed Hc2
  (try wp_auto)
  (try (rw [show decide (s = W64 0) = false by simpa using Hs0]; wp_auto))
  (try rw [decide_eq_false Hnn])
  (try simp only [Hnn, ↓reduceIte, decide_false, Bool.false_eq_true])
  (try wp_auto)
  wp_apply wp_bytes_to_string b bs q $$ Hb as Hb
  (try wp_auto)
  wp_apply wp_udpDest p ip port $$ Hp
  (try wp_auto)
  wp_bind (ExternalOp _ _ _)
  iapply wp_udp_Send s la bs ip port a $$ %Hv Hsock
  imod HAU with ⟨%ms, Hel, Hk⟩
  imodintro
  iexists ms
  iframe Hel
  iintro %r %ms' %Hr Hel
  imod Hk $$ %r %ms' %Hr Hel with HQ
  imodintro
  by_cases hr : r = W64 0
  · subst hr
    wp_auto
    have hd : decide (W64 0 = errCode none) = true := by decide
    rw [hd]
    iapply HΦ
    iframe Hb
    iexists true
    iframe HQ
    ileft
    ipureintro
    exact ⟨rfl, rfl, rfl⟩
  · (try wp_auto)
    (try rw [decide_eq_false hr])
    (try simp only [hr, decide_false, ↓reduceIte, Bool.false_eq_true])
    (try wp_auto)
    (try rw [udp_Addr_ty_eq])
    (try wp_auto)
    wp_apply wp_udpErr go!"write" c s lad _ r go!"sendto" $$ Hc
    iintro %err #Herr
    (try wp_auto)
    iapply HΦ
    iframe Hb
    iexists false
    have hne : decide (r = errCode none) = false := decide_eq_false hr
    rw [hne]
    iframe HQ
    iright
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iexists lad
    iexact Herr

end proof

end net
end Perennial
