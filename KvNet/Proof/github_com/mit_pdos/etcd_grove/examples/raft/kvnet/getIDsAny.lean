/-
Proof of `KvNet/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvnet/getIDsAny.lean`: the count
(`getUint64.specAny`), the length check, then the loop, the rest holding at least the words still to read,
the words read so far `acc` (`bs.drop 8 = u64sLe acc ++ suf`), with the wand back to `b`.
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getIDsAny
public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.getUint64Any

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]

theorem getIDs.wp_proofAny (wp_getUint64 : getUint64.specAny (GF := GF) (hG := hG)) :
    getIDs.specAny (GF := GF) (hG := hG) := by
  intro b dq bs
  wp_start as Hb
  try wp_auto
  wp_apply wp_getUint64 b dq bs $$ [$Hb] as %n %rest %ok Hr
  cases ok with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hr with ⟨%Hsh, Hb⟩
    obtain ⟨Hshort, Hnil⟩ := Hsh
    try wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
  | true =>
  simp only [↓reduceIte]
  icases Hr with ⟨%Hbs, Hrest, Hback⟩
  ihave %Hrl := ownSlice_len _ _ _ $$ Hrest
  try wp_auto
  by_cases hlong : uint.Z (rest.len / W64 8) < uint.Z n
  · rw [decide_eq_true hlong]
    try wp_auto
    ihave Hb := Hback $$ Hrest
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe
  rw [decide_eq_false hlong]
  try wp_auto
  have Hrl' : sint.Z rest.len = (bs.drop 8).length := by
    have := Hrl.1; have := Hrl.2; word
  have Hn8 : 8 * uint.nat n ≤ (bs.drop 8).length := by
    have : uint.Z (rest.len / W64 8) = (bs.drop 8).length / 8 := by
      have := Hrl.2; word
    have hz : (uint.nat n : Int) = uint.Z n := by word
    rw [this] at hlong; omega
  ihave IH : iprop(∃ (j : w64) (sv rv : GoSlice) (acc : List w64) (suf : List w8),
      "i" ∷ i_ptr ↦ j ∗ "ids" ∷ ids_ptr ↦ sv ∗ "rest" ∷ rest_ptr ↦ rv ∗
      "Hsv" ∷ sv ↦* acc ∗ "Hcap" ∷ ownSliceCap w64 sv (DFrac.own 1) ∗
      "Hrv" ∷ rv ↦*{dq} suf ∗
      "Hback" ∷ (rv ↦*{dq} suf -∗ b ↦*{dq} bs) ∗
      "%Hj" ∷ ⌜bs.drop 8 = u64sLe acc ++ suf ∧ acc.length = uint.nat j ∧
        8 * (uint.nat n - uint.nat j) ≤ suf.length ∧ uint.nat j ≤ uint.nat n⌝)
    $$ [i ids rest Hrest Hback]
  · iexists W64 0, _, rest, [], bs.drop 8
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    ipureintro
    refine ⟨rfl, rfl, ?_, Nat.zero_le _⟩
    simpa using Hn8
  wp_for IH
  obtain ⟨Hdrop, Hacc, Hsuf, Hjn⟩ := Hj
  wp_if_destruct
  · have Hin : uint.nat j < uint.nat n := by word
    try wp_auto
    wp_apply wp_getUint64 rv dq suf $$ [$Hrv] as %x %rest2 %ok2 Hr2
    cases ok2 with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      icases Hr2 with ⟨%Hsh, -⟩
      obtain ⟨Hshort, -⟩ := Hsh
      exfalso; omega
    | true =>
    simp only [↓reduceIte]
    icases Hr2 with ⟨%Hsx, Hrest2, Hw⟩
    try wp_auto
    wp_apply wp_slice_literal (V := w64) [x]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hsv $Hcap $Hsl2] as %sv' ⟨Hsv, Hcap, -⟩
    try wp_auto
    wp_for_post
    iframe
    iexists j + W64 1, sv', rest2, acc ++ [x], suf.drop 8
    have Hj1 : uint.nat (j + W64 1) = uint.nat j + 1 := by word
    have Hsl : suf.length = 8 + (suf.drop 8).length := by
      rw [List.length_drop]; omega
    iframe
    isplitl
    · iintro Hr2
      ihave Hr := Hw $$ Hr2
      iapply Hback $$ Hr
    ipureintro
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [Hdrop, u64sLe_snoc, List.append_assoc]; congr 1
    · rw [List.length_append, Hacc, Hj1]; rfl
    · rw [Hj1]; omega
    · rw [Hj1]; omega
  · have Hjk : uint.nat j = uint.nat n := by
      have : ¬ uint.Z j < uint.Z n := by word
      have h1 : (uint.nat j : Int) = uint.Z j := by word
      have h2 : (uint.nat n : Int) = uint.Z n := by word
      omega
    try wp_auto
    iapply HΦ
    simp only [↓reduceIte]
    iexists acc, suf
    iframe
    ipureintro
    have Hnw : n = W64 acc.length := by rw [Hacc, Hjk]; word
    have Htk : bs = u64Le n ++ bs.drop 8 := Hbs
    rw [Htk, Hdrop, encIDs, ← Hnw, List.append_assoc]

end proof

end raft_kvnet
end EtcdGrove
end Perennial
