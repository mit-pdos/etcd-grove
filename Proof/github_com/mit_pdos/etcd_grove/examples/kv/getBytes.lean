/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/getBytes.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.getBytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

theorem getBytes.wp_proof : getBytes.spec (GF := GF) (hG := hG) := by
  intro b dq x r Hx
  wp_start as Hb
  try wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  have Hpl : (putB x ++ r).length = 8 + x.length + r.length := by
    simp [putB, u64Le_length]; omega
  have Hbl : sint.Z b.len = 8 + x.length + r.length := by
    rw [Hpl] at Hlen; have := Hlen.1; word
  rw [decide_eq_false (by rw [Hbl]; show ¬ (_ < (8 : Int)); omega)]
  try wp_auto
  ihave Hb := (show (b ↦*{dq} (putB x ++ r) : IProp GF) ⊣⊢ b ↦*{dq} (u64Le (W64 x.length) ++ (x ++ r)) by
    simp only [putB, List.append_assoc]; exact .rfl).1 $$ Hb
  wp_apply encoding.binary.wp_LittleEndian_Uint64 b (u64Le (W64 x.length)) dq (x ++ r)
    (u64Le_length _) $$ [$Hb] as Hb
  rw [u64Le_to_word]
  have Hxz : uint.Z (W64 x.length) = x.length := by word
  try wp_auto
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
  iframe Hb2 Hb3
  iintro Hb2 Hb3
  ihave Hb2 := E2.2 $$ Hb2
  ihave Hb3 := E3.2 $$ Hb3
  simp only [putB, List.append_assoc]
  iapply (ownSlice_slice (W64 8) (W64 8 + W64 x.length) b dq _ Hrng).2
  iframe

end proof

end kv
end EtcdGrove
end Perennial
