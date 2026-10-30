/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/getMap.lean`. Lean-first (no Rocq
counterpart). (2026-10-22: the first half of `decodeState`'s proof until then, before any rest.)
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.getMap
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.getBytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

theorem getMap.wp_proof (wp_getBytes : getBytes.spec (GF := GF) (hG := hG)) :
    getMap.spec (GF := GF) (hG := hG) := by
  intro b dq kvs r Hkvs
  wp_start as Hb
  try wp_auto
  wp_apply wp_map_make1 (K := GoString) (V := GoString) as %mK HK
  try wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  have Hel : (encMap kvs ++ r).length = 8 + (encKVs kvs).length + r.length := by
    simp [encMap, u64Le_length]; omega
  have Hbl : sint.Z b.len = 8 + (encKVs kvs).length + r.length := by
    rw [Hel] at Hlen; have := Hlen.1; word
  rw [decide_eq_false (by rw [Hbl]; show ¬ (_ < (8 : Int)); omega)]
  try wp_auto
  ihave Hb := (show (b ↦*{dq} (encMap kvs ++ r) : IProp GF) ⊣⊢
      b ↦*{dq} (u64Le (W64 kvs.length) ++ (encKVs kvs ++ r)) by
    simp only [encMap, List.append_assoc]; exact .rfl).1 $$ Hb
  wp_apply encoding.binary.wp_LittleEndian_Uint64 b (u64Le (W64 kvs.length)) dq _
    (u64Le_length _) $$ [$Hb] as Hb
  rw [u64Le_to_word]
  try wp_auto
  have H8 : sint.Z (W64 8) = 8 := rfl
  rw [ite_eq_left (by rw [H8, Hbl]; refine ⟨by decide, by omega, by omega⟩)]
  try wp_auto
  have Hb8 : 0 ≤ sint.Z (W64 8) ∧ sint.Z (W64 8) ≤ sint.Z b.len := by rw [H8, Hbl]; omega
  icases (ownSlice_split_all (W64 8) b dq _ Hb8).1 $$ Hb with ⟨Hb1, Hb2⟩
  have Hd8 : (u64Le (W64 kvs.length) ++ (encKVs kvs ++ r)).drop (sint.nat (W64 8)) =
      encKVs kvs ++ r :=
    List.drop_left' (u64Le_length _)
  have E0 : (slice.slice b w8 (W64 8) b.len ↦*{dq} (u64Le (W64 kvs.length) ++
      (encKVs kvs ++ r)).drop (sint.nat (W64 8)) : IProp GF) ⊣⊢
      slice.slice b w8 (W64 8) b.len ↦*{dq} (encKVs kvs ++ r) := by
    rw [Hd8]; exact .rfl
  ihave Hb2 := E0.1 $$ Hb2
  -- the bindings
  ihave IK : iprop(∃ (i : w64) (cur : GoSlice) (K : GMap GoString GoString),
      "i" ∷ i_ptr ↦ i ∗ "b" ∷ b_ptr ↦ cur ∗
      "Hcur" ∷ cur ↦*{dq} (encKVs (kvs.drop (uint.nat i)) ++ r) ∗
      "Hback" ∷ (cur ↦*{dq} (encKVs (kvs.drop (uint.nat i)) ++ r) -∗
        b ↦*{dq} (encMap kvs ++ r)) ∗
      "HK" ∷ mK ↦$ K ∗
      "%HKv" ∷ ⌜(∀ k, K !! k = (kvs.take (uint.nat i)).lookup k) ∧ uint.nat i ≤ kvs.length⌝)
    $$ [i b Hb1 Hb2 HK]
  · iexists W64 0, _, ∅
    iframe
    simp only [show uint.nat (W64 0) = 0 from rfl, List.drop_zero, List.take_zero]
    iframe
    isplitl
    · iintro Hb2
      ihave Hb2 := E0.2 $$ Hb2
      ihave Hb := (ownSlice_split_all (W64 8) b dq _ Hb8).2 $$ [$Hb1 $Hb2]
      simp only [encMap, List.append_assoc]
      iexact Hb
    ipureintro; exact ⟨fun k => rfl, Nat.zero_le _⟩
  wp_for IK
  have Hkl63 := Hkvs.2.1
  wp_if_destruct
  · have Hin : uint.nat i < kvs.length := by
      have h1 : uint.Z (W64 (kvs.length : Int)) = kvs.length := by word
      rw [h1] at Hif; word
    obtain ⟨p, Hp⟩ : ∃ p, kvs[uint.nat i]? = some p := ⟨_, List.getElem?_eq_getElem Hin⟩
    have Hdrop : kvs.drop (uint.nat i) = p :: kvs.drop (uint.nat i + 1) := by
      rw [List.drop_eq_getElem_cons Hin]
      rw [List.getElem?_eq_getElem Hin] at Hp
      rw [Option.some.inj Hp]
    have Hpl := Hkvs.2.2 p (List.mem_of_getElem? Hp)
    have EC : (cur ↦*{dq} (encKVs (kvs.drop (uint.nat i)) ++ r) : IProp GF) ⊣⊢
        cur ↦*{dq} (putB p.1 ++ (putB p.2 ++ (encKVs (kvs.drop (uint.nat i + 1)) ++ r))) := by
      rw [Hdrop, encKVs_cons]; simp only [List.append_assoc]; exact .rfl
    ihave Hcur := EC.1 $$ Hcur
    try wp_auto
    wp_apply wp_getBytes cur dq p.1 _ Hpl.1 $$ [$Hcur] as %kb %rest ⟨Hk, Hrest, Hw1⟩
    try wp_auto
    wp_apply wp_getBytes rest dq p.2 _ Hpl.2 $$ [$Hrest] as %vb %rest2 ⟨Hv, Hrest2, Hw2⟩
    try wp_auto
    wp_apply wp_bytes_to_string vb p.2 dq $$ [$Hv] as Hv
    try wp_auto
    wp_apply wp_bytes_to_string kb p.1 dq $$ [$Hk] as Hk
    wp_apply wp_mapInsert $$ [$HK] as HK
    try wp_auto
    wp_for_post
    iframe
    iexists i + W64 1, rest2, <[p.1 := p.2]> K
    have Hi1 : uint.nat (i + W64 1) = uint.nat i + 1 := by word
    rw [Hi1]
    iframe
    isplitl [Hback Hw1 Hw2 Hk Hv]
    · iintro Hr2
      ihave Hr := Hw2 $$ Hv Hr2
      ihave Hc := Hw1 $$ Hk Hr
      ihave Hc := EC.2 $$ Hc
      iapply Hback $$ Hc
    ipureintro
    refine ⟨fun k => ?_, by omega⟩
    rw [lookup_take_succ kvs (uint.nat i) p Hp Hkvs.1 k, GMap.lookup_insert_eq_iff]
    by_cases hk : p.1 = k
    · subst hk; simp
    · simp [hk, Ne.symm hk, HKv.1 k]
  · have Hie : uint.nat i = kvs.length := by
      have h1 : uint.Z (W64 (kvs.length : Int)) = kvs.length := by word
      rw [h1] at Hif; have := HKv.2; word
    have Hdn : kvs.drop (uint.nat i) = [] := by rw [Hie, List.drop_length]
    have HKv' : ∀ k, K !! k = kvs.lookup k := by
      intro k; rw [HKv.1 k, Hie, List.take_length]
    have EC : (cur ↦*{dq} (encKVs (kvs.drop (uint.nat i)) ++ r) : IProp GF) ⊣⊢
        cur ↦*{dq} r := by
      rw [Hdn]; simp only [encKVs, List.nil_append]; exact .rfl
    ihave Hcur := EC.1 $$ Hcur
    try wp_auto
    iapply HΦ
    iframe Hcur
    isplitl [Hback]
    · iintro Hc
      ihave Hc := EC.2 $$ Hc
      iapply Hback $$ Hc
    iexists K
    iframe HK
    ipureintro; exact HKv'

end proof

end kvreconf
end EtcdGrove
end Perennial
