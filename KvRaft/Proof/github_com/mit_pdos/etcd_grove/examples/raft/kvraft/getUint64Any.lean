/- Lean-first (no Rocq counterpart).

Proof of `KvRaft/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvraft/getUint64Any.lean`: the short
case returns at once; otherwise the bytes are `u64Le x ++ rest` for `x` the word of the first eight
(`leToU64_le`), and the proof is `getUint64.wp_proof`'s.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.getUint64Any

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

theorem getUint64.wp_proofAny : getUint64.specAny (GF := GF) (hG := hG) := by
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
    iframe Hb
    ipureintro; exact ⟨hshort, by first | rfl | trivial⟩
  -- eight bytes or more: the word of the first eight, then the rest
  have Htk : (bs.take 8).length = 8 := by rw [List.length_take]; omega
  generalize Hx : leToU64 (bs.take 8) = x
  have Hbs : bs = u64Le x ++ bs.drop 8 := by
    rw [← Hx, leToU64_le _ Htk, List.take_append_drop]
  generalize Hr : bs.drop 8 = r at Hbs
  subst Hbs
  have Hpl : (u64Le x ++ r).length = 8 + r.length := by
    simp [u64Le_length]
  have Hbl : sint.Z b.len = 8 + r.length := by
    rw [Hpl] at Hlen; have := Hlen.1; word
  rw [decide_eq_false (by rw [Hbl]; show ¬ (_ < (8 : Int)); omega)]
  try wp_auto
  wp_apply encoding.binary.wp_LittleEndian_Uint64 b (u64Le x) dq r
    (u64Le_length _) $$ [$Hb] as Hb
  rw [u64Le_to_word]
  try wp_auto
  have H8 : sint.Z (W64 8) = 8 := rfl
  rw [ite_eq_left (by rw [Hbl, H8]; refine ⟨by decide, by omega, by omega⟩)]
  try wp_auto
  have Hrng : 0 ≤ sint.Z (W64 8) ∧ sint.Z (W64 8) ≤ sint.Z b.len ∧
      sint.Z b.len ≤ sint.Z b.len := by
    rw [Hbl, H8]; refine ⟨by decide, by omega, by omega⟩
  icases (ownSlice_slice (W64 8) b.len b dq _ Hrng).1 $$ Hb with ⟨Hb1, Hb2, Hb3⟩
  have Hn8 : sint.nat (W64 8) = 8 := rfl
  have Hdr : (u64Le x ++ r).drop (sint.nat b.len) = [] := by
    apply List.drop_eq_nil_of_le
    rw [Hpl]; have := Hbl; word
  have Hsub : subslice (sint.nat (W64 8)) (sint.nat b.len) (u64Le x ++ r) = r := by
    rw [Hn8]
    simp only [subslice, List.drop_take]
    rw [List.drop_left' (u64Le_length _)]
    apply List.take_of_length_le
    rw [← Hlen.1, Hpl]; omega
  have Hd8 : (u64Le x ++ r).drop 8 = r := List.drop_left' (u64Le_length _)
  have E2 : (slice.slice b w8 (W64 8) b.len ↦*{dq}
      subslice (sint.nat (W64 8)) (sint.nat b.len) (u64Le x ++ r) : IProp GF) ⊣⊢
      slice.slice b w8 (W64 8) b.len ↦*{dq} r := by rw [Hsub]; exact .rfl
  ihave Hb2 := E2.1 $$ Hb2
  iapply HΦ
  simp only [↓reduceIte, Hd8]
  isplitr
  · ipureintro; trivial
  iframe Hb2
  iintro Hb2
  ihave Hb2 := E2.2 $$ Hb2
  iapply (ownSlice_slice (W64 8) b.len b dq _ Hrng).2
  iframe

end proof

end kvraft
end EtcdGrove
end Perennial
