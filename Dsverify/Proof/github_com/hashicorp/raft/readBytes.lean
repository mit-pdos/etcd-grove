/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/readBytes.lean (241f27e).
-/
/-
The proof of `raft.readBytes`.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.readBytes
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

theorem github_com.hashicorp.raft.readBytes.wp_proof
    (wp_readUint64 : github_com.hashicorp.raft.readUint64.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.readBytes.spec (GF := GF) (hG := hG) := by
  intro b xs rest dq
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  have hxl : xs.length < 2 ^ 63 := by
    have h := Hlen.1; simp only [List.length_append, le64_length] at h; word
  rw [List.append_assoc]
  wp_auto
  wp_apply wp_readUint64 $$ [$Hb] as %b1 ⟨Hb1, Hback⟩
  ihave %Hlen1 := ownSlice_len _ _ _ $$ Hb1
  ihave %Hwf1 := ownSlice_wf _ _ _ $$ Hb1
  simp only [List.length_append] at Hlen1
  wp_if_destruct
  · exfalso; word
  icases (ownSlice_split_all (W64 xs.length) b1 dq _ ⟨by word, by word⟩).1 $$ Hb1 with ⟨H1, H2⟩
  have hn : sint.nat (W64 (xs.length : Int)) = xs.length := by word
  rw [hn, List.take_left, List.drop_left]
  wp_apply (wp_slice_make2 (V := w8)) as %out ⟨Hout, -⟩
  · ipureintro; word
  rw [if_pos (by word)]
  wp_auto
  wp_apply (wp_slice_copy (V := w8)) $$ [$Hout $H1] as %m ⟨-, Hout, H1⟩
  rw [if_pos (by word)]
  wp_auto
  rw [hn, List.length_replicate, List.take_length, List.drop_of_length_le (by simp), List.append_nil]
  iapply HΦ
  iframe Hout H2
  iintro H2
  iapply Hback
  iapply (ownSlice_split_all (W64 xs.length) b1 dq _ ⟨by word, by word⟩).2
  rw [hn, List.take_left, List.drop_left]
  iframe

end proof

end Perennial
