/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/putIDs.lean`. Lean-first (no
Rocq counterpart): the count (`putUint64`), then the loop over the ids, the buffer holding the
prefix's words (`u64sLe`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.putIDs
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.putUint64

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

theorem putIDs.wp_proof (wp_putUint64 : putUint64.spec (GF := GF) (hG := hG)) :
    putIDs.spec (GF := GF) (hG := hG) := by
  intro buf ids B xs dq
  wp_start as ⟨Hbuf, Hcap, Hids⟩
  try wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hids
  wp_apply wp_putUint64 buf B ids.len $$ [$Hbuf $Hcap] as %b0 ⟨Hb, Hbcap⟩
  try wp_auto
  ihave IH : iprop(∃ (j : w64) (bv : GoSlice) (x : w64),
      "i" ∷ i_ptr ↦ j ∗ "buf" ∷ buf_ptr ↦ bv ∗
      "Hb" ∷ bv ↦* (B ++ u64Le ids.len ++ u64sLe (xs.take (sint.nat j))) ∗
      "Hbcap" ∷ ownSliceCap w8 bv (DFrac.own 1) ∗ "id" ∷ id_ptr ↦ x ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z ids.len⌝)
    $$ [i buf Hb Hbcap id]
  · iexists W64 0, b0, _
    iframe
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, u64sLe, List.append_nil]
    iframe
    ipureintro; exact ⟨by decide, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hjl : sint.nat j < xs.length := by rw [Hlen.1]; word
    obtain ⟨x0, Hx0⟩ : ∃ x0, xs[sint.nat j]? = some x0 := ⟨_, List.getElem?_eq_getElem Hjl⟩
    try wp_auto
    rw [ite_eq_left (by omega)]
    wp_apply wp_load_slice_index ids (sint.Z j) xs dq x0 Hj.1 $$ [$Hids] as Hids
    · ipureintro; exact Hx0
    try wp_auto
    wp_apply wp_putUint64 bv _ x0 $$ [$Hb $Hbcap] as %b1 ⟨Hb, Hbcap⟩
    try wp_auto
    wp_for_post
    iframe
    iexists j + W64 1, b1, x0
    have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have Htk : xs.take (sint.nat j + 1) = xs.take (sint.nat j) ++ [x0] := by
      rw [List.take_add_one, Hx0]; rfl
    rw [Hj1, Htk, u64sLe_snoc]
    simp only [List.append_assoc]
    iframe
    ipureintro; constructor <;> word
  · have Hjk : sint.nat j = xs.length := by rw [Hlen.1]; word
    rw [Hjk, List.take_length] at *
    try wp_auto
    iapply HΦ
    iframe
    have Hxl : W64 xs.length = ids.len := by rw [Hlen.1]; have := Hlen.2; word
    unfold encIDs
    rw [Hxl, List.append_assoc]
    iexact Hb

end proof

end kvdurable
end EtcdGrove
end Perennial
