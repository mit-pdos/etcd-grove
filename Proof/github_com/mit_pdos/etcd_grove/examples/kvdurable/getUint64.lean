/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/getUint64.lean`. Lean-first (no
Rocq counterpart): `getBytes`'s first half (the length check, Perennial's `LittleEndian.Uint64`,
the slice after the word).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.getUint64

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]

theorem getUint64.wp_proof : getUint64.spec (GF := GF) (hG := hG) := by
  intro b dq x r
  wp_start as Hb
  try wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
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
  have E2 : (slice.slice b w8 (W64 8) b.len ↦*{dq}
      subslice (sint.nat (W64 8)) (sint.nat b.len) (u64Le x ++ r) : IProp GF) ⊣⊢
      slice.slice b w8 (W64 8) b.len ↦*{dq} r := by rw [Hsub]; exact .rfl
  ihave Hb2 := E2.1 $$ Hb2
  iapply HΦ
  iframe Hb2
  iintro Hb2
  ihave Hb2 := E2.2 $$ Hb2
  iapply (ownSlice_slice (W64 8) b.len b dq _ Hrng).2
  iframe

end proof

end kvdurable
end EtcdGrove
end Perennial
