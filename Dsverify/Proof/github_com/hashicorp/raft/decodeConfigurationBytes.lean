/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/decodeConfigurationBytes.lean (241f27e).
-/
/-
The proof of `raft.decodeConfigurationBytes`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.decodeConfigurationBytes
public import Dsverify.Spec.github_com.hashicorp.raft.readUint64
public import Dsverify.Spec.github_com.hashicorp.raft.readBytes
public import Dsverify.Proof.github_com.hashicorp.raft.EncodingLemmas

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto

theorem github_com.hashicorp.raft.decodeConfigurationBytes.wp_proof
    (wp_readUint64 : github_com.hashicorp.raft.readUint64.spec (GF := GF) (hG := hG))
    (wp_readBytes : github_com.hashicorp.raft.readBytes.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.decodeConfigurationBytes.spec (GF := GF) (hG := hG) := by
  intro b ss dq
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  rw [encodeServers_eq] at Hlen ⊢
  wp_auto
  have hsl : ss.length < 2 ^ 63 := by
    have h1 := Hlen.1; have h2 := length_le_flatMap_encSrv ss
    simp only [List.length_append, le64_length] at h1; word
  wp_apply wp_readUint64 $$ [$Hb] as %b1 ⟨Hb1, Hback⟩
  ihave HI : (∃ (k : w64) (bb sl : GoSlice),
      "i" ∷ i_ptr ↦ k ∗ "b" ∷ b_ptr ↦ bb ∗ "err" ∷ err_ptr ↦ interface.nil ∗
      "servers" ∷ servers_ptr ↦ sl ∗ "Hsl" ∷ sl ↦* ss.take (uint.nat k) ∗
      "Hcap" ∷ ownSliceCap Server sl (DFrac.own 1) ∗
      "Hb" ∷ bb ↦*{dq} (ss.drop (uint.nat k)).flatMap encSrv ∗
      "Hback" ∷ (bb ↦*{dq} (ss.drop (uint.nat k)).flatMap encSrv -∗
        b ↦*{dq} le64 (W64 ss.length) ++ ss.flatMap encSrv) ∗
      "%Hk" ∷ ⌜uint.nat k ≤ ss.length⌝ : IProp GF) $$ [i b err servers Hb1 Hback]
  · iexists W64 0, b1, slice.nil
    simp only [show uint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero]
    iframe
    isplitl
    · iapply ownSlice_nil
    isplitl
    · iapply ownSliceCap_nil
    ipureintro; omega
  wp_for HI
  wp_if_destruct
  · have hk : uint.nat k < ss.length := by word
    list_elem ss (uint.nat k) as sv
    rw [drop_flatMap_encSrv ss _ sv Hsv_lookup]
    wp_apply wp_readUint64 $$ [$Hb] as %b2 ⟨Hb, Hw1⟩
    wp_apply wp_readBytes $$ [$Hb] as %id %b3 ⟨Hid, Hb, Hw2⟩
    wp_apply wp_readBytes $$ [$Hb] as %addr %b4 ⟨Haddr, Hb, Hw3⟩
    wp_apply (wp_bytes_to_string id sv.ID' (DFrac.own 1)) $$ [$Hid] as Hid
    wp_apply (wp_bytes_to_string addr sv.Address' (DFrac.own 1)) $$ [$Haddr] as Haddr
    wp_apply (wp_slice_literal (V := Server) [sv])
    isplitr
    · ipureintro; rfl
    iintro %slp ⟨Hlit, -⟩
    wp_apply (wp_slice_append (V := Server)) $$ [$Hsl $Hcap $Hlit] as %sl2 ⟨Hsl, Hcap, -⟩
    wp_for_post
    iframe
    iexists k + W64 1, b4, sl2
    rw [show uint.nat (k + W64 1) = uint.nat k + 1 by word, List.take_succ, Hsv_lookup]
    iframe
    isplitl
    · iintro H
      iapply Hback; iapply Hw1; iapply Hw2; iapply Hw3; iexact H
    ipureintro; omega
  · rw [show uint.nat k = ss.length by word, List.take_length, List.drop_length]
    iapply HΦ
    iframe
    iapply Hback
    simp only [List.flatMap_nil]
    iexact Hb

end proof

end Perennial
