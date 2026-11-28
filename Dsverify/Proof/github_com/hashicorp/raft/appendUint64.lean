/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/appendUint64.lean (241f27e).
-/
/-
The proof of `raft.appendUint64`.
-/
module

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

theorem github_com.hashicorp.raft.appendUint64.wp_proof :
    github_com.hashicorp.raft.appendUint64.spec (GF := GF) (hG := hG) := by
  intro b bs x
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  ihave HI : (∃ (k : w64) (b' : GoSlice),
      "i" ∷ i_ptr ↦ k ∗ "b" ∷ b_ptr ↦ b' ∗
      "Hb" ∷ b' ↦* (bs ++ (le64 x).take (sint.nat k)) ∗ "Hcap" ∷ ownSliceCap w8 b' (DFrac.own 1) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ 8⌝ : IProp GF) $$ [i b Hb Hcap]
  · iexists W64 0, b
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.append_nil]
    iframe
    ipureintro; decide
  wp_for HI
  wp_if_destruct
  · wp_apply (wp_slice_literal (V := w8) [W8 (uint.Z (x >>> (W64 8 * k)))])
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply (wp_slice_append (V := w8)) $$ [$Hb $Hcap $Hsl] as %b2 ⟨Hb, Hcap, -⟩
    wp_for_post
    iframe
    iexists k + W64 1, b2
    have hk8 : sint.nat k < 8 := by word
    rw [show sint.nat (k + W64 1) = sint.nat k + 1 by word, le64_take_succ x _ hk8,
      W8_uintZ, shiftr_mul8 x k (by word), show k.toNat = sint.nat k by word, List.append_assoc]
    iframe
    ipureintro; word
  · rw [show sint.nat k = 8 by word, le64_take_8]
    iapply HΦ
    iframe

end proof

end Perennial
