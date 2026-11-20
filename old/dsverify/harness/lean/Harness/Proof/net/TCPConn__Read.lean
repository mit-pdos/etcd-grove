/-
The proof of `Spec/net/TCPConn__Read.lean`: the promoted method, then the model over
`NetConn.wp_Read` and the copy into the buffer (`wp_slice_copy`).
-/
module

public import Harness.Spec.net.TCPConn__Read

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netConnExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.Assumptions] [net.model.Assumptions]

theorem net.TCPConn.Read.wp_proof : net.TCPConn.Read.spec (GF := GF) (hG := hG) := by
  intro c cid side b bs P R
  unfold net.ownTCPConn
  wp_start as ⟨⟨%fd, #Hfd, #HFD, #Hc, -⟩, Htok, Hb⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  rw [method_unfold]
  wp_auto
  wp_apply net.wp_fdOf $$ Hfd
  wp_apply net.wp_idSide $$ HFD
  wp_apply net.wp_idSide $$ HFD
  wp_apply NetConn.wp_Read cid side b.len P R $$ Htok as %data %code ⟨%Hd, Htok⟩
  wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  have hm : b.len.toNat = bs.length := by
    rw [Hlen.1]; have := Hlen.2; word
  have hle : data.length ≤ bs.length := hm ▸ Hd.1
  -- `n = W64 |data|`: when nothing is read, `copy` of an empty source returns 0
  -- (`wp_slice_copy_of_len_zero`); `wp_slice_copy` gives only `sint.nat n`, which a
  -- negative `n` would also meet
  by_cases hd : data = []
  · subst hd
    have hz : sl.len = W64 0 := by
      have h0 : sint.nat sl.len = 0 := by simpa using Hsll.1.symm
      have h1 := Hsll.2
      word
    wp_apply wp_slice_copy_of_len_zero (V := w8) b sl hz
    wp_apply net.wp_connResult $$ [$HFD] as %err #Herr
    ihave %Hnil := net.connErr_nil $$ Herr
    iapply HΦ
    iexists [], code
    simp only [List.nil_append, List.length_nil, List.drop_zero]
    iframe Hb Htok Herr
    ipureintro
    refine ⟨rfl, Nat.zero_le _, Hnil, fun _ => trivial, fun h hne => Hd.2.2 (Hnil.1 h) ?_⟩
    rw [hm]; intro h0; exact hne (List.eq_nil_of_length_eq_zero h0)
  wp_apply wp_slice_copy (V := w8) b bs sl data $$ [$Hb $Hsl] as %n ⟨%Hn, Hb, -⟩
  wp_apply net.wp_connResult $$ [$HFD] as %err #Herr
  ihave %Hnil := net.connErr_nil $$ Herr
  have htake : data.take bs.length = data := List.take_of_length_le hle
  have himp : (b ↦* (data.take bs.length ++ bs.drop data.length) : IProp GF) ⊢
      b ↦* (data ++ bs.drop data.length) := by rw [htake]
  ihave Hb := himp $$ Hb
  have hn : sint.nat n = data.length := by rw [Hn]; exact Nat.min_eq_right hle
  have hpos : 0 < data.length := List.length_pos_iff.mpr hd
  have hlt : data.length < 2 ^ 63 := by
    have h2 : bs.length = (sint.Z b.len).toNat := Hlen.1
    have h3 : sint.Z b.len < 2 ^ 63 := by word
    clear Hn; omega
  have hneq : n = W64 data.length := by
    have h1 : (sint.Z n).toNat = data.length := hn
    have h2 : sint.Z n = (data.length : Int) := by omega
    apply BitVec.eq_of_toInt_eq
    rw [show BitVec.toInt n = sint.Z n from rfl, h2]
    have : ((data.length : Int) : w64).toInt = (data.length : Int) := by
      rw [BitVec.toInt_intCast]; apply Int.bmod_eq_of_le <;> omega
    exact this.symm
  iapply HΦ
  iexists data, code
  iframe Hb Htok Herr
  ipureintro
  refine ⟨hneq, hle, Hnil, fun h => Hd.2.1 (fun hc => h (Hnil.2 hc)), fun h hne => Hd.2.2 (Hnil.1 h) ?_⟩
  rw [hm]; intro h0; exact hne (List.eq_nil_of_length_eq_zero h0)

end proof

end Perennial
