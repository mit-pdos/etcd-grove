/-
Proof of `KvRaft/Spec/github_com/mit_pdos/etcd_grove/examples/raft/kvraft/getMapAny.lean`: the count's word
(`leToU64_le`), then the bindings (`getBytes.specAny` twice per binding), the bytes not yet read given back
through a wand.
-/
module

public import KvRaft.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.getMapAny
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

theorem getMap.wp_proofAny (wp_getBytes : getBytes.specAny (GF := GF) (hG := hG)) :
    getMap.specAny (GF := GF) (hG := hG) := by
  intro b dq bs
  wp_start as Hb
  try wp_auto
  wp_apply wp_map_make1 (K := GoString) (V := GoString) as %mK HK
  try wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  by_cases hshort : bs.length < 8
  · rw [decide_eq_true (show sint.Z b.len < sint.Z (W64 8) by have := Hlen.1; word)]
    try wp_auto
    iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    itrivial
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
  have H8 : sint.Z (W64 8) = 8 := rfl
  rw [ite_eq_left (by rw [H8, Hbl]; refine ⟨by decide, by omega, by omega⟩)]
  try wp_auto
  have Hb8 : 0 ≤ sint.Z (W64 8) ∧ sint.Z (W64 8) ≤ sint.Z b.len := by rw [H8, Hbl]; omega
  icases (ownSlice_split_all (W64 8) b dq _ Hb8).1 $$ Hb with ⟨Hb1, Hb2⟩
  have Hd8 : (u64Le n ++ rest).drop (sint.nat (W64 8)) = rest := List.drop_left' (u64Le_length _)
  have E0 : (slice.slice b w8 (W64 8) b.len ↦*{dq} (u64Le n ++ rest).drop (sint.nat (W64 8)) :
      IProp GF) ⊣⊢ slice.slice b w8 (W64 8) b.len ↦*{dq} rest := by
    rw [Hd8]; exact .rfl
  ihave Hb2 := E0.1 $$ Hb2
  -- the bindings
  ihave IK : iprop(∃ (i : w64) (cur : GoSlice) (suf : List w8) (K : GMap GoString GoString),
      "i" ∷ i_ptr ↦ i ∗ "b" ∷ b_ptr ↦ cur ∗ "Hcur" ∷ cur ↦*{dq} suf ∗
      "Hback" ∷ (cur ↦*{dq} suf -∗ b ↦*{dq} (u64Le n ++ rest)) ∗ "HK" ∷ mK ↦$ K)
    $$ [i b Hb1 Hb2 HK]
  · iexists W64 0, _, rest, ∅
    iframe
    iintro Hb2
    ihave Hb2 := E0.2 $$ Hb2
    iapply (ownSlice_split_all (W64 8) b dq _ Hb8).2 $$ [$Hb1 $Hb2]
  wp_for IK
  wp_if_destruct
  · try wp_auto
    wp_apply wp_getBytes cur dq suf $$ [$Hcur] as %kb %rest1 %ok1 Hk
    cases ok1 with
    | false =>
      try wp_auto
      wp_for_post
      iapply HΦ
      simp only [Bool.false_eq_true, ↓reduceIte]
      itrivial
    | true =>
      simp only [↓reduceIte]
      icases Hk with ⟨%x1, %r1, %Hs1, Hk, Hrest1, Hw1⟩
      try wp_auto
      wp_apply wp_getBytes rest1 dq r1 $$ [$Hrest1] as %vb %rest2 %ok2 Hv
      cases ok2 with
      | false =>
        try wp_auto
        wp_for_post
        iapply HΦ
        simp only [Bool.false_eq_true, ↓reduceIte]
        itrivial
      | true =>
        simp only [↓reduceIte]
        icases Hv with ⟨%x2, %r2, %Hs2, Hv, Hrest2, Hw2⟩
        try wp_auto
        wp_apply wp_bytes_to_string vb x2 dq $$ [$Hv] as Hv
        try wp_auto
        wp_apply wp_bytes_to_string kb x1 dq $$ [$Hk] as Hk
        wp_apply wp_mapInsert $$ [$HK] as HK
        try wp_auto
        wp_for_post
        iframe
        iexists i + W64 1, rest2, r2, _
        iframe
        iintro Hr2
        ihave Hr := Hw2 $$ Hv Hr2
        ihave Hc := Hw1 $$ Hk Hr
        iapply Hback $$ Hc
  · try wp_auto
    iapply HΦ
    simp only [↓reduceIte]
    iexists K, suf
    iframe

end proof

end kvraft
end EtcdGrove
end Perennial
