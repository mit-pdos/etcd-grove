/-
Port of `election_proof/proof_JointConfig__IDs.v`.

`for _, cc := range c { for id := range cc { m[id] = struct{}{} } }`: the outer loop
ranges over the array value `c` (read once), `array.forRange 2`, which unfolds to a
`for:` over the index; element 0 is the incoming config `v`, element 1 the nil map, whose
range loop is the pure step `wp_map_nil_for_range`. The inner loop is Perennial's
`wp_map_for_range`, which hands the map's points-to back after the loop, as Rocq's
(`iIntros "HP Hvoters"`). `cc` and `id` are assigned every iteration (neither escapes),
so they are allocated once and existentially quantified inside the invariants.
-/
module

public import Spec.go_etcd_io.raft.v3.quorum.JointConfig__IDs

@[expose] public section

noncomputable section

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem quorum.JointConfig.IDs.wp_proof :
    quorum.JointConfig.IDs.spec (GF := GF) (hG := hG) := by
  intro jc v vm dqv Harr
  obtain ⟨arr⟩ := jc
  simp only at Harr
  subst Harr
  wp_start as Hvoters
  -- the value method's call, then `GoAlloc JointConfig` gives `"c" ∷ c_ptr ↦ jc`
  wp_auto
  -- `m := map[uint64]struct{}{}`
  wp_apply wp_map_make1 (K := w64) (V := Unit) as %mref Hmref
  -- `for _, cc := range c`: `c` was read into the array value, `cc` allocated, and the
  -- loop unfolded to a `for:` over the index `i`
  ihave HI : (∃ (j : w64) (ccv : quorum.MajorityConfig) (idm : GMap w64 Unit),
      "i" ∷ i_ptr ↦ j ∗ "cc" ∷ cc_ptr ↦ ccv ∗ "m" ∷ m_ptr ↦ mref ∗
      "Hmref" ∷ mref ↦$ idm ∗ "Hvoters" ∷ v ↦${dqv} vm ∗
      "%Hj" ∷ ⌜(j = W64 0 ∧ idm = ∅) ∨ (j = W64 1 ∧ domSet idm = domSet vm) ∨
        (j = W64 2 ∧ domSet idm = domSet vm)⌝ : IProp GF) $$ [i cc m Hmref Hvoters]
  · iexists W64 0, _, ∅
    iframe
    ipureintro; left; exact ⟨rfl, rfl⟩
  wp_for HI
  rcases Hj with ⟨rfl, rfl⟩ | ⟨rfl, Hdom⟩ | ⟨rfl, Hdom⟩ <;> wp_if_destruct <;>
    try (exfalso; word)
  · -- `cc = c[0] = v`: `for id := range cc { m[id] = struct{}{} }`. The invariant
    -- carries the domain of the partial map: after `i` iterations it is the first `i`
    -- keys of the enumeration. (`wp_for` already read `c[0]` into `cc` and allocated `id`.)
    wp_func_lits
    iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (x : w64)
        (idm : GMap w64 Unit),
        "%Hi" ∷ ⌜0 ≤ i⌝ ∗
        "%Hidm" ∷ ⌜∀ k, k ∈ domSet idm ↔ k ∈ keys.take i.toNat⌝ ∗
        "id" ∷ id_ptr ↦ x ∗
        "m" ∷ m_ptr ↦ mref ∗
        "Hmref" ∷ mref ↦$ idm)) $$ Hvoters
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [id m Hmref]
    · iexists zero_val w64, ∅
      simp only [named]
      iframe id m Hmref
      ipureintro
      refine ⟨Int.le_refl _, fun k => ?_⟩
      simp only [Int.toNat_zero, List.take_zero, List.not_mem_nil, iff_false]
      rw [GMap.elem_of_dom]
      rintro ⟨v, hv⟩
      simp at hv
    isplitr
    · imodintro
      iintro %i %key %vv ⟨%Hkey, %Hvv⟩ HP
      iNamed HP
      wp_auto
      wp_apply wp_mapInsert $$ Hmref as Hmref
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists key, _
      simp only [named]
      iframe id m Hmref
      ipureintro
      refine ⟨by omega, fun k => ?_⟩
      have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
        rw [show (i + 1).toNat = i.toNat + 1 by omega]
        rw [List.take_add_one, Hkey]; rfl
      rw [Htake, List.mem_append, List.mem_singleton, ← Hidm, GMap.elem_of_dom,
        GMap.elem_of_dom]
      by_cases hk : key = k
      · subst hk; simp
      · rw [GMap.lookup_insert_ne _ _ hk]
        constructor
        · intro h; exact .inl h
        · rintro (h | h)
          · exact h
          · exact absurd h.symm hk
    -- the range is over: `domSet idm` is every key, i.e. `domSet vm`
    iintro HP Hvoters
    iNamed HP
    rw [Int.toNat_natCast, ← Hklen, List.take_length] at Hidm
    wp_for_post
    simp only [named]
    iframe HΦ
    iexists W64 1, _, _
    iframe
    ipureintro; right; left; refine ⟨rfl, ?_⟩
    apply GMap.set_eq; intro k
    rw [Hidm, Hkset, GMap.elem_of_dom, Option.isSome_iff_exists]
  · -- `cc = c[1] = nil`: ranging over the nil map is the pure step `wp_map_nil_for_range`
    wp_func_lits
    wp_auto
    wp_for_post
    simp only [named]
    iframe HΦ
    iexists W64 2, _, _
    iframe
    ipureintro; right; right; exact ⟨rfl, Hdom⟩
  · -- `return m`
    iapply HΦ
    iframe Hvoters Hmref
    ipureintro
    exact Hdom

end proof

end EtcdGrove
end Perennial
