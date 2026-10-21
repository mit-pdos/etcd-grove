/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvwitness/decode.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import RaftWitness.Spec.github_com.mit_pdos.etcd_grove.examples.kvwitness.decode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvwitness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvwitness.Assumptions]

theorem decode.wp_proof : decode.spec (GF := GF) (hG := hG) := by
  intro b d dq
  wp_start as Hb
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  wp_if_destruct
  · have Hd : decodeOp d = none := by
      unfold decodeOp; rw [ite_eq_right (by obtain ⟨h1, h2⟩ := Hlen; word)]
    unfold decodeRet; rw [Hd]
    iapply HΦ
    iexact Hb
  have H25 : 25 ≤ d.length := by obtain ⟨h1, h2⟩ := Hlen; word
  have Hbl : 25 ≤ sint.Z b.len := by word
  rw [ite_eq_left (by word)]
  icases (ownSlice_split_all (W64 17) b dq d ⟨by decide, by word⟩).1 $$ Hb with ⟨Hb1, Hb2⟩
  ihave Hb2 := (show (slice.slice b w8 (W64 17) b.len ↦*{dq} d.drop (sint.nat (W64 17)) : IProp GF) ⊣⊢
      slice.slice b w8 (W64 17) b.len ↦*{dq} ((d.drop 17).take 8 ++ (d.drop 17).drop 8) by
    rw [List.take_append_drop]; exact .rfl).1 $$ Hb2
  wp_apply encoding.binary.wp_LittleEndian_Uint64 _ ((d.drop 17).take 8) dq ((d.drop 17).drop 8)
    (by simp; omega) $$ [$Hb2] as Hb2
  rw [List.take_append_drop]
  ihave Hb2 : slice.slice b w8 (W64 17) b.len ↦*{dq} d.drop (sint.nat (W64 17)) $$ [Hb2]
  · rw [show sint.nat (W64 17) = 17 from rfl]; iexact Hb2
  ihave Hb := (ownSlice_split_all (W64 17) b dq d ⟨by decide, by word⟩).2 $$ [$Hb1 $Hb2]
  try wp_auto
  generalize Hn : leToU64 ((d.drop 17).take 8) = n
  wp_if_destruct
  · have Hd : decodeOp d = none := by
      unfold decodeOp; rw [ite_eq_left H25, Hn, ite_eq_right (by word)]
    unfold decodeRet; rw [Hd]
    iapply HΦ
    iexact Hb
  have Hnl : uint.Z n ≤ (d.length : Int) - 25 := by word
  have Hd : decodeOp d = some (leToU64 (d.take 8), leToU64 ((d.drop 8).take 8),
      d.getD 16 (W8 0), (d.drop 25).take (uint.nat n), (d.drop 25).drop (uint.nat n)) := by
    unfold decodeOp; rw [ite_eq_left H25, Hn, ite_eq_left Hnl]
  unfold decodeRet; rw [Hd]
  simp only []
  ihave Hb := (show (b ↦*{dq} d : IProp GF) ⊣⊢ b ↦*{dq} (d.take 8 ++ d.drop 8) by
    rw [List.take_append_drop 8 d]; exact .rfl).1 $$ Hb
  wp_apply encoding.binary.wp_LittleEndian_Uint64 b (d.take 8) dq (d.drop 8)
    (by simp; omega) $$ [$Hb] as Hb
  rw [List.take_append_drop 8 d]
  rw [ite_eq_left (by word)]
  icases (ownSlice_split_all (W64 8) b dq d ⟨by decide, by word⟩).1 $$ Hb with ⟨Hb1, Hb2⟩
  ihave Hb2 := (show (slice.slice b w8 (W64 8) b.len ↦*{dq} d.drop (sint.nat (W64 8)) : IProp GF) ⊣⊢
      slice.slice b w8 (W64 8) b.len ↦*{dq} ((d.drop 8).take 8 ++ (d.drop 8).drop 8) by
    rw [List.take_append_drop]; exact .rfl).1 $$ Hb2
  wp_apply encoding.binary.wp_LittleEndian_Uint64 _ ((d.drop 8).take 8) dq ((d.drop 8).drop 8)
    (by simp; omega) $$ [$Hb2] as Hb2
  rw [List.take_append_drop]
  ihave Hb2 : slice.slice b w8 (W64 8) b.len ↦*{dq} d.drop (sint.nat (W64 8)) $$ [Hb2]
  · rw [show sint.nat (W64 8) = 8 from rfl]; iexact Hb2
  ihave Hb := (ownSlice_split_all (W64 8) b dq d ⟨by decide, by word⟩).2 $$ [$Hb1 $Hb2]
  try wp_auto
  rw [ite_eq_left (by word)]
  wp_apply wp_load_slice_index b (sint.Z (W64 16)) d dq (d.getD 16 (W8 0)) (by decide)
    $$ [$Hb] as Hb
  · ipureintro
    have h16 : (sint.Z (W64 16)).toNat = 16 := rfl
    rw [h16, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  try wp_auto
  have Hn25 : sint.Z (W64 25 + n) = 25 + uint.Z n := by word
  have Hn25n : sint.nat (W64 25 + n) = 25 + uint.nat n := by word
  rw [ite_eq_left (by rw [Hn25]; refine ⟨by decide, by word, by word⟩)]
  icases (ownSlice_slice (W64 25) (W64 25 + n) b dq d ⟨by decide, by rw [Hn25]; word,
    by rw [Hn25]; word⟩).1 $$ Hb with ⟨Hb1, Hb2, Hb3⟩
  have Hsub : subslice (sint.nat (W64 25)) (sint.nat (W64 25 + n)) d =
      (d.drop 25).take (uint.nat n) := by
    rw [Hn25n, show sint.nat (W64 25) = 25 from rfl]
    simp only [subslice, List.drop_take]
    congr 1; omega
  rw [Hsub]
  wp_apply wp_bytes_to_string _ ((d.drop 25).take (uint.nat n)) dq $$ [$Hb2] as Hb2
  ihave Hb2 : slice.slice b w8 (W64 25) (W64 25 + n) ↦*{dq}
      subslice (sint.nat (W64 25)) (sint.nat (W64 25 + n)) d $$ [Hb2]
  · rw [Hsub]; iexact Hb2
  ihave Hb := (ownSlice_slice (W64 25) (W64 25 + n) b dq d ⟨by decide, by rw [Hn25]; word,
    by rw [Hn25]; word⟩).2 $$ [$Hb1 $Hb2 $Hb3]
  try wp_auto
  rw [ite_eq_left (by rw [Hn25]; refine ⟨by word, by word, Hwf.2⟩)]
  icases (ownSlice_split_all (W64 25 + n) b dq d ⟨by word, by word⟩).1 $$ Hb with ⟨Hb1, Hb2⟩
  have Hdr : d.drop (sint.nat (W64 25 + n)) = (d.drop 25).drop (uint.nat n) := by
    rw [Hn25n, List.drop_drop]
  rw [Hdr]
  wp_apply wp_bytes_to_string _ ((d.drop 25).drop (uint.nat n)) dq $$ [$Hb2] as Hb2
  rw [← Hdr]
  ihave Hb := (ownSlice_split_all (W64 25 + n) b dq d ⟨by word, by word⟩).2 $$ [$Hb1 $Hb2]
  try wp_auto
  iapply HΦ
  iexact Hb

end proof

end kvwitness
end EtcdGrove
end Perennial
