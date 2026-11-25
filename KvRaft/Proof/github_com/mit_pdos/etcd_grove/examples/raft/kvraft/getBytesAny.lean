/-
Proof of `KvRaft/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvraft/getBytesAny.lean`: the short case
and a length past the bytes return at once; otherwise the bytes are `putB x ++ r` for `x` the next `n`
bytes (`n` the word of the first eight, `leToU64_le`), and the proof is `getBytes.wp_proof`'s.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.getBytesAny

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvraft

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.Assumptions]

theorem getBytes.wp_proofAny : getBytes.specAny (GF := GF) (hG := hG) := by
  intro b dq bs
  wp_start as Hb
  try wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  by_cases hshort : bs.length < 8
  · rw [decide_eq_true (show sint.Z b.len < sint.Z (W64 8) by have := Hlen.1; word)]
    try wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    iexact Hb
  have Htk : (bs.take 8).length = 8 := by rw [List.length_take]; omega
  generalize Hn : leToU64 (bs.take 8) = n
  have Hbs : bs = u64Le n ++ bs.drop 8 := by
    rw [← Hn, leToU64_le _ Htk, List.take_append_drop]
  generalize Hrest : bs.drop 8 = rest at Hbs
  subst Hbs
  have Hpl : (u64Le n ++ rest).length = 8 + rest.length := by simp [u64Le_length]
  have Hbl : sint.Z b.len = 8 + rest.length := by
    rw [Hpl] at Hlen; have := Hlen.1; word
  rw [decide_eq_false (by rw [Hbl]; show ¬ (_ < (8 : Int)); omega)]
  try wp_auto
  wp_apply encoding.binary.wp_LittleEndian_Uint64 b (u64Le n) dq rest
    (u64Le_length _) $$ [$Hb] as Hb
  rw [u64Le_to_word]
  try wp_auto
  by_cases hlong : (rest.length : Int) < uint.Z n
  · rw [decide_eq_true (show uint.Z (b.len - W64 8) < uint.Z n by word)]
    try wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    iexact Hb
  -- the bytes are `putB x ++ r`
  have hle0 : uint.Z n ≤ rest.length := by omega
  have hle : uint.nat n ≤ rest.length := by word
  generalize Hx : rest.take (uint.nat n) = x
  generalize Hr : rest.drop (uint.nat n) = r
  have Hxl : x.length = uint.nat n := by
    rw [← Hx, List.length_take, Nat.min_eq_left hle]
  have Hnx : n = W64 x.length := by rw [Hxl]; word
  have Hrxr : rest = x ++ r := by rw [← Hx, ← Hr, List.take_append_drop]
  subst Hrxr
  have HxL : (x.length : Int) < 2 ^ 63 := by have := Hlen.1; simp [u64Le_length] at *; word
  rw [Hnx]
  have Hxz : uint.Z (W64 x.length) = x.length := by word
  have Hbl' : sint.Z b.len = 8 + x.length + r.length := by
    rw [Hbl, List.length_append]; push_cast; omega
  rw [decide_eq_false (by rw [Hxz]; word)]
  try wp_auto
  have H8n : sint.Z (W64 8 + W64 x.length) = 8 + x.length := by word
  have H8 : sint.Z (W64 8) = 8 := rfl
  rw [ite_eq_left (by rw [H8n, H8]; refine ⟨by decide, by omega, by omega⟩)]
  try wp_auto
  rw [ite_eq_left (by rw [H8n]; refine ⟨by omega, by omega, by omega⟩)]
  try wp_auto
  have Hrng : 0 ≤ sint.Z (W64 8) ∧ sint.Z (W64 8) ≤ sint.Z (W64 8 + W64 x.length) ∧
      sint.Z (W64 8 + W64 x.length) ≤ sint.Z b.len := by
    rw [H8n, H8]; refine ⟨by decide, by omega, by omega⟩
  icases (ownSlice_slice (W64 8) (W64 8 + W64 x.length) b dq _ Hrng).1 $$ Hb with ⟨Hb1, Hb2, Hb3⟩
  have Hn8 : sint.nat (W64 8) = 8 := rfl
  have Hn8x : sint.nat (W64 8 + W64 x.length) = 8 + x.length := by word
  have Hsub : subslice (sint.nat (W64 8)) (sint.nat (W64 8 + W64 x.length))
      (u64Le (W64 x.length) ++ (x ++ r)) = x := by
    rw [Hn8, Hn8x]
    simp only [subslice, List.drop_take]
    rw [show 8 + x.length - 8 = x.length by omega, List.drop_left' (u64Le_length _)]
    try exact List.take_left' rfl
  have Hdr : (u64Le (W64 x.length) ++ (x ++ r)).drop (sint.nat (W64 8 + W64 x.length)) = r := by
    rw [Hn8x, ← List.append_assoc]
    exact List.drop_left' (by simp [u64Le_length])
  have E2 : (slice.slice b w8 (W64 8) (W64 8 + W64 x.length) ↦*{dq}
      subslice (sint.nat (W64 8)) (sint.nat (W64 8 + W64 x.length))
        (u64Le (W64 x.length) ++ (x ++ r)) : IProp GF) ⊣⊢
      slice.slice b w8 (W64 8) (W64 8 + W64 x.length) ↦*{dq} x := by rw [Hsub]; exact .rfl
  have E3 : (slice.slice b w8 (W64 8 + W64 x.length) b.len ↦*{dq}
      (u64Le (W64 x.length) ++ (x ++ r)).drop (sint.nat (W64 8 + W64 x.length)) : IProp GF) ⊣⊢
      slice.slice b w8 (W64 8 + W64 x.length) b.len ↦*{dq} r := by rw [Hdr]; exact .rfl
  ihave Hb2 := E2.1 $$ Hb2
  ihave Hb3 := E3.1 $$ Hb3
  iapply HΦ
  simp only [↓reduceIte]
  iexists x, r
  isplitr
  · ipureintro; simp only [putB, List.append_assoc]
  iframe Hb2 Hb3
  iintro Hb2 Hb3
  ihave Hb2 := E2.2 $$ Hb2
  ihave Hb3 := E3.2 $$ Hb3
  iapply (ownSlice_slice (W64 8) (W64 8 + W64 x.length) b dq _ Hrng).2
  iframe

end proof

end kvraft
end EtcdGrove
end Perennial
