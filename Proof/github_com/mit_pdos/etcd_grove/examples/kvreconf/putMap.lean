/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvreconf/putMap.lean`. Lean-first (no Rocq
counterpart). (2026-10-22: the first half of `encodeState`'s proof until then, over any `buf`.)
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.putMap
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.putBytes
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvreconf.sortStrings

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

/-- A key's binding in the map `K` (a key it lacks: `[]`, Go's lookup). -/
def kvOfM (K : GMap GoString GoString) (k : GoString) : GoString × GoString := (k, (K !! k).getD [])

theorem lookup_map_kvOfM (K : GMap GoString GoString) (ks : List GoString) (k : GoString) :
    (ks.map (kvOfM K)).lookup k = if k ∈ ks then some ((K !! k).getD []) else none := by
  induction ks with
  | nil => simp
  | cons k' ks ih =>
    simp only [List.map_cons, kvOfM, List.lookup_cons, List.mem_cons]
    by_cases h : k = k'
    · subst h; simp
    · have h' : (k == k') = false := by simpa using h
      simp only [h', ih]
      by_cases hk : k ∈ ks <;> simp [hk, h]

theorem W64_sint_nat (x : w64) (h : 0 ≤ sint.Z x) : W64 ((sint.nat x : Nat) : Int) = x := by word

theorem sint_nat_lt (x : w64) : ((sint.nat x : Nat) : Int) < 2 ^ 63 := by word

theorem putMap.wp_proof (wp_putBytes : putBytes.spec (GF := GF) (hG := hG))
    (wp_sortStrings : sortStrings.spec (GF := GF) (hG := hG)) :
    putMap.spec (GF := GF) (hG := hG) := by
  intro buf B mK K dq
  wp_start as ⟨Hbuf, Hbcap0, HK⟩
  try wp_auto
  -- the keys
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List GoString) (i : Int) => iprop(∃ (ksl : GoSlice) (x : GoString),
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗ "keys" ∷ keys_ptr ↦ ksl ∗ "Hsl" ∷ ksl ↦* keys.take i.toNat ∗
      "Hcap" ∷ ownSliceCap GoString ksl (DFrac.own 1) ∗ "k" ∷ k_ptr ↦ x)) $$ HK
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [keys k]
  · iexists _, _
    simp only [named]
    iframe
    isplitr; · ipureintro; exact Int.le_refl _
    simp only [Int.toNat_zero, List.take_zero]
    isplitl; · iapply ownSlice_nil
    iapply ownSliceCap_nil
  isplitr
  · imodintro
    iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
    iNamed HP
    try wp_auto
    wp_apply wp_slice_literal (V := GoString) [key]
    isplitr
    · ipureintro; rfl
    iintro %sl2 ⟨Hsl2, -⟩
    wp_apply wp_slice_append $$ [$Hsl $Hcap $Hsl2] as %sl' ⟨Hsl, Hcap, -⟩
    try wp_auto
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists sl', key
    simp only [named]
    iframe
    isplitr; · ipureintro; omega
    have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
    rw [Htake]; iexact Hsl
  iintro HP HK
  iNamed HP
  rw [Int.toNat_natCast, ← Hklen, List.take_length]
  try wp_auto
  wp_apply wp_sortStrings ksl keys $$ [$Hsl] as ⟨%ks, Hsl, %Hks⟩
  try wp_auto
  ihave %Hksl := ownSlice_len _ _ _ $$ Hsl
  -- the key count
  ihave Hn := slice_array (GF := GF) n_ptr _ _ (by decide) $$ n
  rw [show (zero_val (GoArray w8 8)).arr = List.replicate 8 (W8 0) ++ [] from rfl,
    show W64 (8 : Int) = W64 8 from rfl] at *
  simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show W64 8 - W64 0 = W64 8 from rfl]
  wp_apply encoding.binary.wp_LittleEndian_PutUint64 _ (List.replicate 8 (W8 0)) [] _ rfl
    $$ [$Hn] as Hn
  try wp_auto
  simp only [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
    show W64 8 - W64 0 = W64 8 from rfl, List.append_nil]
  ihave Hn : slice.mk n_ptr (W64 8) (W64 8) ↦* u64Le ksl.len $$ [Hn]
  · rw [show u64Le ksl.len = u64Le ksl.len ++ [] from (List.append_nil _).symm]; iexact Hn
  wp_apply wp_slice_append buf B _ (u64Le ksl.len) (DFrac.own 1) $$ [$Hbuf $Hbcap0 $Hn]
    as %b0 ⟨Hb, Hbcap, Hn⟩
  try wp_auto
  -- the bindings
  ihave IH : iprop(∃ (j : w64) (bv : GoSlice) (x : GoString),
      "i" ∷ i_ptr ↦ j ∗ "buf" ∷ buf_ptr ↦ bv ∗
      "Hb" ∷ bv ↦* (B ++ u64Le ksl.len ++ encKVs ((ks.take (sint.nat j)).map (kvOfM K))) ∗
      "Hbcap" ∷ ownSliceCap w8 bv (DFrac.own 1) ∗ "k" ∷ k_ptr ↦ x ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z ksl.len ∧
        ∀ p ∈ (ks.take (sint.nat j)).map (kvOfM K), (p.1.length : Int) < 2 ^ 63 ∧
          (p.2.length : Int) < 2 ^ 63⌝)
    $$ [i buf Hb Hbcap k]
  · iexists W64 0, b0, _
    iframe
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.map_nil, encKVs,
      List.append_nil]
    iframe
    ipureintro; exact ⟨by decide, by word, fun _ h => by cases h⟩
  wp_for IH
  wp_if_destruct
  · have Hjl : sint.nat j < ks.length := by rw [Hksl.1]; word
    obtain ⟨key, Hkey⟩ : ∃ key, ks[sint.nat j]? = some key := ⟨_, List.getElem?_eq_getElem Hjl⟩
    try wp_auto
    rw [ite_eq_left (by omega)]
    wp_apply wp_load_slice_index ksl (sint.Z j) ks (DFrac.own 1) key Hj.1 $$ [$Hsl] as Hsl
    · ipureintro; exact Hkey
    try wp_auto
    wp_apply wp_string_to_bytes key as %ksb ⟨Hksb, -⟩
    ihave %Hkl := ownSlice_len _ _ _ $$ Hksb
    wp_apply wp_putBytes bv ksb _ key (DFrac.own 1) $$ [$Hb $Hbcap $Hksb] as %b1 ⟨Hb, Hbcap, -⟩
    try wp_auto
    wp_apply wp_map_lookup1 go.string go.string mK K key dq $$ HK as HK
    wp_apply wp_string_to_bytes ((K !! key).getD (zero_val GoString)) as %vsb ⟨Hvsb, -⟩
    ihave %Hvl := ownSlice_len _ _ _ $$ Hvsb
    wp_apply wp_putBytes b1 vsb _ _ (DFrac.own 1) $$ [$Hb $Hbcap $Hvsb] as %b2 ⟨Hb, Hbcap, -⟩
    try wp_auto
    wp_for_post
    iframe
    iexists j + W64 1, b2, key
    have Hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
    have Htk : ks.take (sint.nat j + 1) = ks.take (sint.nat j) ++ [key] := by
      rw [List.take_add_one, Hkey]; rfl
    rw [Hj1, Htk, List.map_append, List.map_singleton, encKVs_snoc]
    simp only [List.append_assoc]
    iframe
    ipureintro
    refine ⟨by word, by word, ?_⟩
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact Hj.2.2 p hp
    · simp only [List.mem_singleton] at hp; subst hp
      simp only [kvOfM]
      have hz : (zero_val GoString) = [] := rfl
      rw [hz] at Hvl
      exact ⟨by have := Hkl.1; word, by have := Hvl.1; word⟩
  · have Hjk : sint.nat j = ks.length := by rw [Hksl.1]; word
    have Htk : ks.take (sint.nat j) = ks := by rw [Hjk, List.take_length]
    rw [Htk] at Hj
    ihave Hb : bv ↦* (B ++ encMap (ks.map (kvOfM K))) $$ [Hb]
    · have Hkl : W64 (ks.map (kvOfM K)).length = ksl.len := by
        rw [List.length_map, Hksl.1]; exact W64_sint_nat _ Hksl.2
      rw [show B ++ encMap (ks.map (kvOfM K)) =
          B ++ u64Le ksl.len ++ encKVs ((ks.take (sint.nat j)).map (kvOfM K)) by
        unfold encMap; rw [Hkl, Htk, List.append_assoc]]
      iexact Hb
    try wp_auto
    iapply HΦ
    iframe HK Hbcap
    iexists ks.map (kvOfM K)
    iframe Hb
    ipureintro
    have Hksn : ks.Nodup := Hks.nodup_iff.2 Hknodup
    refine ⟨⟨?_, ?_, Hj.2.2⟩, ?_⟩
    · rw [List.map_map, show Prod.fst ∘ kvOfM K = id from rfl, List.map_id]; exact Hksn
    · rw [List.length_map, Hksl.1]; exact sint_nat_lt _
    · intro k
      rw [lookup_map_kvOfM]
      have hm : k ∈ ks ↔ (K !! k).isSome := by rw [Hks.mem_iff]; exact Hkset k
      by_cases hk : k ∈ ks
      · rw [if_pos hk]
        obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hm.1 hk)
        rw [hv]; rfl
      · rw [if_neg hk]
        cases h : K !! k with
        | none => rfl
        | some v => exact absurd (hm.2 (by rw [h]; rfl)) hk

end proof

end kvreconf
end EtcdGrove
end Perennial
