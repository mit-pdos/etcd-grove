/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/getIDs.lean`. Lean-first (no
Rocq counterpart): the count (`getUint64`), the length check (the rest holds at least the count's
words), then the loop, the rest holding the words not yet read (`u64sLe (xs.drop j)`), with the
wand back to `b`, and the fresh slice the ones read.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.getIDs
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

theorem getIDs.wp_proof (wp_getUint64 : getUint64.spec (GF := GF) (hG := hG)) :
    getIDs.spec (GF := GF) (hG := hG) := by
  intro b dq xs r
  wp_start as Hb
  try wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  have Hel : (encIDs xs ++ r).length = 8 + 8 * xs.length + r.length := by
    simp only [List.length_append, encIDs_length]
  have Hxs : (xs.length : Int) < 2 ^ 60 := by
    have : sint.Z b.len < 2 ^ 63 := by word
    have h2 := Hlen.1
    rw [Hel] at h2
    have : ((8 + 8 * xs.length + r.length : Nat) : Int) = sint.Z b.len := by
      rw [h2]; have := Hlen.2; word
    omega
  ihave Hb := (show (b ↦*{dq} (encIDs xs ++ r) : IProp GF) ⊣⊢
      b ↦*{dq} (u64Le (W64 xs.length) ++ (u64sLe xs ++ r)) by
    simp only [encIDs, List.append_assoc]; exact .rfl).1 $$ Hb
  wp_apply wp_getUint64 b dq (W64 xs.length) _ $$ [$Hb] as %rest ⟨Hrest, Hback⟩
  ihave %Hrl := ownSlice_len _ _ _ $$ Hrest
  try wp_auto
  have Hnl : uint.Z (W64 xs.length) = xs.length := by word
  have Hrl' : sint.Z rest.len = 8 * xs.length + r.length := by
    have h := Hrl.1
    simp only [List.length_append, u64sLe_length] at h
    have := Hrl.2
    have : ((8 * xs.length + r.length : Nat) : Int) = sint.Z rest.len := by rw [h]; word
    omega
  rw [decide_eq_false (by
    show ¬ (uint.Z (rest.len / W64 8) < uint.Z (W64 xs.length))
    rw [Hnl]
    have : uint.Z (rest.len / W64 8) = (8 * xs.length + r.length) / 8 := by
      have := Hrl.2; have := Hrl'; word
    rw [this]; omega)]
  try wp_auto
  ihave IH : iprop(∃ (j : w64) (sv rv : GoSlice),
      "i" ∷ i_ptr ↦ j ∗ "ids" ∷ ids_ptr ↦ sv ∗ "rest" ∷ rest_ptr ↦ rv ∗
      "Hsv" ∷ sv ↦* xs.take (uint.nat j) ∗ "Hcap" ∷ ownSliceCap w64 sv (DFrac.own 1) ∗
      "Hrv" ∷ rv ↦*{dq} (u64sLe (xs.drop (uint.nat j)) ++ r) ∗
      "Hback" ∷ (rv ↦*{dq} (u64sLe (xs.drop (uint.nat j)) ++ r) -∗
        b ↦*{dq} (encIDs xs ++ r)) ∗
      "%Hj" ∷ ⌜uint.nat j ≤ xs.length⌝)
    $$ [i ids rest Hrest Hback]
  · iexists W64 0, _, rest
    iframe
    simp only [show uint.nat (W64 0) = 0 from rfl, List.take_zero]
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    ipureintro; exact Nat.zero_le _
  wp_for IH
  wp_if_destruct
  · have Hin : uint.nat j < xs.length := by rw [Hnl] at Hif; word
    obtain ⟨x0, Hx0⟩ : ∃ x0, xs[uint.nat j]? = some x0 := ⟨_, List.getElem?_eq_getElem Hin⟩
    have Hdrop : xs.drop (uint.nat j) = x0 :: xs.drop (uint.nat j + 1) := by
      rw [List.drop_eq_getElem_cons Hin]
      rw [List.getElem?_eq_getElem Hin] at Hx0
      rw [Option.some.inj Hx0]
    have EC : (rv ↦*{dq} (u64sLe (xs.drop (uint.nat j)) ++ r) : IProp GF) ⊣⊢
        rv ↦*{dq} (u64Le x0 ++ (u64sLe (xs.drop (uint.nat j + 1)) ++ r)) := by
      rw [Hdrop]; simp only [u64sLe, List.append_assoc]; exact .rfl
    ihave Hrv := EC.1 $$ Hrv
    try wp_auto
    wp_apply wp_getUint64 rv dq x0 _ $$ [$Hrv] as %rest2 ⟨Hrest2, Hw⟩
    try wp_auto
    wp_apply wp_slice_literal (V := w64) [x0]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hsv $Hcap $Hsl2] as %sv' ⟨Hsv, Hcap, -⟩
    try wp_auto
    wp_for_post
    iframe
    iexists j + W64 1, sv', rest2
    have Hj1 : uint.nat (j + W64 1) = uint.nat j + 1 := by word
    have Htk : xs.take (uint.nat j + 1) = xs.take (uint.nat j) ++ [x0] := by
      rw [List.take_add_one, Hx0]; rfl
    rw [Hj1, Htk]
    iframe
    isplitl
    · iintro Hr2
      ihave Hr := Hw $$ Hr2
      ihave Hr := EC.2 $$ Hr
      iapply Hback $$ Hr
    ipureintro; omega
  · have Hjk : uint.nat j = xs.length := by
      rw [Hnl] at Hif; have := Hj; word
    rw [Hjk, List.take_length, List.drop_length] at *
    try wp_auto
    iapply HΦ
    iframe Hsv
    simp only [u64sLe, List.nil_append]
    iframe Hrv
    iexact Hback

end proof

end kvdurable
end EtcdGrove
end Perennial
