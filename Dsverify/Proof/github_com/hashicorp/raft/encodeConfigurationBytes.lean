/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/encodeConfigurationBytes.lean (241f27e).
-/
/-
The proof of `raft.encodeConfigurationBytes`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.encodeConfigurationBytes
public import Dsverify.Spec.github_com.hashicorp.raft.appendBytes
public import Dsverify.Spec.github_com.hashicorp.raft.appendUint64
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

theorem github_com.hashicorp.raft.encodeConfigurationBytes.wp_proof
    (wp_appendUint64 : github_com.hashicorp.raft.appendUint64.spec (GF := GF) (hG := hG))
    (wp_appendBytes : github_com.hashicorp.raft.appendBytes.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.encodeConfigurationBytes.spec (GF := GF) (hG := hG) := by
  intro c ss dq
  wp_start as Hs
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  wp_auto
  wp_apply (wp_appendUint64 slice.nil []) $$ [] as %b0 ⟨Hb, Hcap⟩
  · isplitl
    · iapply ownSlice_nil
    · iapply ownSliceCap_nil
  rw [List.nil_append, show c.Servers'.len = W64 (ss.length : Int) by word]
  ihave HI : (∃ (k : w64) (bb : GoSlice) (sv : Server),
      "i" ∷ i_ptr ↦ k ∗ "b" ∷ b_ptr ↦ bb ∗ "s" ∷ s_ptr ↦ sv ∗
      "Hb" ∷ bb ↦* (le64 (W64 ss.length) ++ (ss.take (sint.nat k)).flatMap encSrv) ∗
      "Hcap" ∷ ownSliceCap w8 bb (DFrac.own 1) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z c.Servers'.len⌝ : IProp GF) $$ [i b s Hb Hcap]
  · iexists W64 0, b0, _
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.flatMap_nil, List.append_nil]
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · rw [if_pos (by word)]
    list_elem ss (sint.nat k) as sv'
    wp_apply (wp_load_slice_index c.Servers' (sint.Z k) ss dq sv' Hk.1) $$ [$Hs] as Hs
    · ipureintro; rw [show (sint.Z k).toNat = sint.nat k by word]; exact Hsv'_lookup
    wp_apply wp_appendUint64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
    wp_apply (wp_string_to_bytes sv'.ID') as %sid ⟨Hsid, -⟩
    wp_apply wp_appendBytes $$ [$Hb $Hcap $Hsid] as %b2 ⟨Hb, Hcap, -⟩
    wp_apply (wp_string_to_bytes sv'.Address') as %sad ⟨Hsad, -⟩
    wp_apply wp_appendBytes $$ [$Hb $Hcap $Hsad] as %b3 ⟨Hb, Hcap, -⟩
    wp_for_post
    iframe
    iexists k + W64 1, b3, sv'
    rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word,
      flatMap_take_succ encSrv ss _ sv' Hsv'_lookup]
    simp only [encSrv, List.append_assoc]
    iframe
    ipureintro; word
  · rw [show sint.nat k = ss.length by word, List.take_length]
    iapply HΦ
    rw [encodeServers_eq]
    iframe

end proof

end Perennial
