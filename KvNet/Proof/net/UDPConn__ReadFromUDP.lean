-- The copy for the part `KvNet/` of `Net/Proof/net/UDPConn__ReadFromUDP.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The proof of `Net/Spec/net/UDPConn__ReadFromUDP.lean`: `UDPConn.ReadFromUDP.impl`'s extension
`Recv` takes the caller's update (`Udp.wp_udp_Recv`); the bytes are then copied into the buffer.
-/
module

public import KvNet.Spec.net.UDPConn__ReadFromUDP
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

/-- The arithmetic of the copy: `copy(b, d[:len(b)])` copies `min(len(b), len(d))` bytes. -/
theorem recv_copy (L n : w64) (bs0 d : List w8) (hL : bs0.length = sint.nat L)
    (hL0 : 0 ≤ sint.Z L) (hn : sint.Z n = min bs0.length (d.take L.toNat).length) :
    n.toNat = min L.toNat d.length ∧
      (d.take L.toNat).take bs0.length ++ bs0.drop (d.take L.toNat).length =
        d.take n.toNat ++ bs0.drop n.toNat := by
  have hLt : L.toNat = bs0.length := by
    rw [hL]; simp only [sint.nat, sint.Z] at hL0 ⊢
    have h := BitVec.toInt_eq_toNat_cond L
    split at h <;> omega
  have hnt : n.toNat = min L.toNat d.length := by
    rw [List.length_take, ← hLt] at hn
    simp only [sint.Z] at hn
    have h := BitVec.toInt_eq_toNat_cond n
    split at h <;> omega
  refine ⟨hnt, ?_⟩
  rw [hnt, List.take_take, List.length_take, ← hLt]
  congr 1
  rw [Nat.min_self]
  rcases Nat.le_total L.toNat d.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.take_of_length_le h, List.take_of_length_le (Nat.le_refl _)]

theorem UDPConn.ReadFromUDP.wp_proof : UDPConn.ReadFromUDP.spec (GF := GF) (hG := hG) := by
  intro c s a b bs0 Q
  unfold udpConnAt
  wp_start as ⟨⟨%lad, #Hc, #Hlad, %Hs0, #Hsock⟩, Hb, HAU⟩
  icases ownSlice_len b _ bs0 $$ Hb with %Hlen
  (try wp_method_call)
  (try unfold UDPConn.ReadFromUDP.impl)
  (try unfold model.udpId)
  rw [UDPConn_ty_eq]
  ihave #Hc2 := Hc
  iStructNamed Hc2
  (try wp_auto)
  (try (rw [show decide (s = W64 0) = false by simpa using Hs0]; wp_auto))
  wp_bind (ExternalOp _ _ _)
  iapply wp_udp_Recv s a b.len $$ Hsock
  imod HAU with ⟨%ms, Hel, Hk⟩
  imodintro
  iexists ms
  iframe Hel
  iintro %od %Hod Hel
  imod Hk $$ %od %Hod Hel with HQ
  imodintro
  cases od with
  | none =>
    simp only [recvVal, recvRes]
    wp_auto
    wp_apply wp_udpErr go!"read" c s lad _ _ go!"recvfrom" $$ Hc
    iintro %err #Herr
    (try wp_auto)
    iapply HΦ
    iexists none
    dsimp only
    iframe HQ Hb
    isplitr
    · ipureintro; exact ⟨rfl, rfl⟩
    iexists lad
    iexact Herr
  | some d =>
    simp only [recvVal, recvRes]
    wp_auto
    wp_apply wp_string_to_bytes (d.take b.len.toNat) as %sl ⟨Hsl, -⟩
    wp_apply wp_slice_copy_int b bs0 sl (d.take b.len.toNat) (DFrac.own 1) $$ [Hb Hsl]
      as %n ⟨%Hn, Hb, -⟩
    · iframe
    (try wp_auto)
    wp_apply wp_anyUDPAddr
    iintro %pa -
    (try wp_auto)
    obtain ⟨hn, heq⟩ := recv_copy b.len n bs0 d Hlen.1 Hlen.2 Hn
    iapply HΦ
    iexists some d
    dsimp only
    iframe HQ
    rw [heq]
    iframe Hb
    ipureintro
    exact ⟨hn, rfl⟩

end proof

end net
end Perennial
