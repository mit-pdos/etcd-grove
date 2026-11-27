/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/readUint64.lean (241f27e).
-/
/-
The proof of `raft.readUint64`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.readUint64
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

theorem github_com.hashicorp.raft.readUint64.wp_proof :
    github_com.hashicorp.raft.readUint64.spec (GF := GF) (hG := hG) := by
  intro b x rest dq
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  have hl8 : 8 ≤ sint.Z b.len := by
    have h := Hlen.1; simp only [List.length_append, le64_length] at h; word
  wp_auto
  wp_if_destruct
  · exfalso; word
  ihave HI : (∃ (k : w64),
      "i" ∷ i_ptr ↦ k ∗ "x" ∷ x_ptr ↦ (x &&& lowMask (sint.nat k)) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ 8⌝ : IProp GF) $$ [i x]
  · iexists W64 0
    rw [show sint.nat (W64 0) = 0 from rfl, lowMask_0]
    rw [show x &&& (0 : w64) = 0 from BitVec.and_zero]
    iframe
    ipureintro; decide
  wp_for HI
  wp_if_destruct
  · have hk8 : sint.nat k < 8 := by word
    rw [if_pos (by word)]
    wp_apply (wp_load_slice_index b (sint.Z k) _ dq ((x >>> (8 * sint.nat k)).setWidth 8) Hk.1)
      $$ [$Hb] as Hb
    · ipureintro
      rw [List.getElem?_append_left (by rw [le64_length]; word)]
      rw [show (sint.Z k).toNat = sint.nat k by word]
      exact le64_getElem x _ hk8
    wp_for_post
    iframe
    iexists k + W64 1
    rw [W64_uintZ_w8, shiftl_mul8 _ k (by word), show k.toNat = sint.nat k by word,
      lowMask_succ x _ hk8, show sint.nat (k + W64 1) = sint.nat k + 1 by word]
    iframe
    ipureintro; word
  · rw [show sint.nat k = 8 by word, lowMask_8]
    ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
    rw [if_pos (by word)]
    wp_auto
    icases (ownSlice_split_all (W64 8) b dq _ ⟨by word, by word⟩).1 $$ Hb with ⟨H1, H2⟩
    have h8 : sint.nat (W64 8) = 8 := rfl
    rw [h8, List.take_left' (le64_length x), List.drop_left' (le64_length x)]
    iapply HΦ
    iframe H2
    iintro H2
    iapply (ownSlice_split_all (W64 8) b dq _ ⟨by word, by word⟩).2
    rw [h8, List.take_left' (le64_length x), List.drop_left' (le64_length x)]
    iframe
end proof

end Perennial
