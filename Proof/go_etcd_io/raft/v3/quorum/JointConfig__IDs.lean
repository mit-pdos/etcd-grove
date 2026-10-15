/-
Proof of `Spec/go_etcd_io/raft/v3/quorum/JointConfig__IDs.lean`. Lean-first (no Rocq counterpart).
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- One step of the union loop: `acc` and the first `i` keys, then key `key` too. -/
theorem union_take_step (mv acc : GMap w64 Unit) (keys : List w64) (i : Int) (key : w64)
    (Hi : 0 ≤ i) (Hkey : keys[i.toNat]? = some key)
    (Hmv : ∀ k, k ∈ domSet mv ↔ k ∈ domSet acc ∨ k ∈ keys.take i.toNat) :
    ∀ k, k ∈ domSet (<[key := ()]> mv) ↔ k ∈ domSet acc ∨ k ∈ keys.take (i + 1).toNat := by
  intro k
  have Htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
    rw [show (i + 1).toNat = i.toNat + 1 by omega]
    rw [List.take_add_one, Hkey]; rfl
  rw [Htake, GMap.dom_insert, GMap.elem_of_union, GMap.elem_of_singleton, Hmv,
    List.mem_append, List.mem_singleton]
  constructor
  · rintro (h | h | h)
    · exact .inr (.inr h)
    · exact .inl h
    · exact .inr (.inl h)
  · rintro (h | h | h)
    · exact .inr (.inl h)
    · exact .inr (.inr h)
    · exact .inl h

/-- The union loop's result: a set map is its domain. -/
theorem union_done (mv acc src : GMap w64 Unit) (keys : List w64)
    (Hkset : ∀ k, k ∈ keys ↔ (src !! k).isSome)
    (Hmv : ∀ k, k ∈ domSet mv ↔ k ∈ domSet acc ∨ k ∈ keys) :
    mv = acc ∪ src := by
  apply GMap.map_eq; intro k
  have := Hmv k
  rw [Hkset, GMap.elem_of_dom, GMap.elem_of_dom] at this
  rw [GMap.lookup_union]
  rcases h1 : mv !! k with _ | ⟨⟩ <;> rcases h2 : acc !! k with _ | ⟨⟩ <;>
    rcases h3 : src !! k with _ | ⟨⟩ <;> simp_all

theorem quorum.JointConfig.IDs.wp_proof :
    quorum.JointConfig.IDs.spec (GF := GF) (hG := hG) := by
  intro p jc v0 v1 s0 s1 dq dq0 dq1 Harr
  obtain ⟨arr⟩ := jc
  simp only at Harr
  subst Harr
  wp_start as ⟨Hp, Hv0, Hv1⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  -- `m := map[uint64]struct{}{}`
  wp_apply wp_map_make1 (K := w64) (V := Unit) as %mref Hmref
  -- `for _, cc := range c`
  ihave HI : (∃ (j : w64) (ccv : quorum.MajorityConfig) (idm : GMap w64 Unit),
      "i" ∷ i_ptr ↦ j ∗ "cc" ∷ cc_ptr ↦ ccv ∗ "m" ∷ m_ptr ↦ mref ∗
      "Hmref" ∷ mref ↦$ idm ∗ "Hv0" ∷ ownIdsetQ v0 dq0 s0 ∗ "Hv1" ∷ ownIdsetQ v1 dq1 s1 ∗
      "%Hj" ∷ ⌜(j = W64 0 ∧ idm = ∅) ∨ (j = W64 1 ∧ idm = ∅ ∪ s0) ∨
        (j = W64 2 ∧ idm = ∅ ∪ s0 ∪ s1)⌝ : IProp GF) $$ [i cc m Hmref Hv0 Hv1]
  · iexists W64 0, _, ∅
    iframe
    ipureintro; left; exact ⟨rfl, rfl⟩
  wp_for HI
  rcases Hj with ⟨rfl, rfl⟩ | ⟨rfl, Hidm⟩ | ⟨rfl, Hidm⟩ <;> wp_if_destruct <;>
    try (exfalso; word)
  · -- `cc = c[0] = v0`
    unfold ownIdsetQ
    icases Hv0 with (⟨%Hnil, %Hs⟩ | Hv0)
    · subst Hnil Hs
      wp_func_lits
      wp_auto
      wp_for_post
      simp only [named]
      iframe HΦ Hp
      iexists W64 0 + W64 1, _, _
      iframe i cc m Hmref Hv1
      isplitl []
      · ileft; ipureintro; simp
      ipureintro; right; left; refine ⟨rfl, ?_⟩
      rw [GMap.mapEmpty_union]
    wp_func_lits
    iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (x : w64)
        (mv : GMap w64 Unit),
        "%Hi" ∷ ⌜0 ≤ i⌝ ∗
        "%Hmv" ∷ ⌜∀ k, k ∈ domSet mv ↔ k ∈ domSet (∅ : GMap w64 Unit) ∨ k ∈ keys.take i.toNat⌝ ∗
        "id" ∷ id_ptr ↦ x ∗
        "m" ∷ m_ptr ↦ mref ∗
        "Hmref" ∷ mref ↦$ mv)) $$ Hv0
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [id m Hmref]
    · iexists zero_val w64, ∅
      simp only [named]
      iframe id m Hmref
      ipureintro
      refine ⟨Int.le_refl _, fun k => ?_⟩
      simp only [Int.toNat_zero, List.take_zero, List.not_mem_nil, _root_.or_false]
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
      exact ⟨by omega, union_take_step mv ∅ keys i key Hi Hkey Hmv⟩
    iintro HP Hv0
    iNamed HP
    rw [Int.toNat_natCast, ← Hklen, List.take_length] at Hmv
    wp_for_post
    simp only [named]
    iframe HΦ Hp
    iexists W64 0 + W64 1, _, _
    iframe i cc m Hmref Hv1
    isplitl [Hv0]
    · iright; iexact Hv0
    ipureintro; right; left; exact ⟨rfl, union_done mv ∅ s0 keys Hkset Hmv⟩
  · -- `cc = c[1] = v1`
    unfold ownIdsetQ
    icases Hv1 with (⟨%Hnil, %Hs⟩ | Hv1)
    · subst Hnil Hs
      wp_func_lits
      wp_auto
      wp_for_post
      simp only [named]
      iframe HΦ Hp
      iexists W64 1 + W64 1, _, _
      iframe i cc m Hmref Hv0
      isplitl []
      · ileft; ipureintro; simp
      ipureintro; right; right; refine ⟨rfl, ?_⟩
      rw [Hidm, GMap.map_union_empty]
    wp_func_lits
    iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (x : w64)
        (mv : GMap w64 Unit),
        "%Hi" ∷ ⌜0 ≤ i⌝ ∗
        "%Hmv" ∷ ⌜∀ k, k ∈ domSet mv ↔ k ∈ domSet idm ∨ k ∈ keys.take i.toNat⌝ ∗
        "id" ∷ id_ptr ↦ x ∗
        "m" ∷ m_ptr ↦ mref ∗
        "Hmref" ∷ mref ↦$ mv)) $$ Hv1
    iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
    isplitl [id m Hmref]
    · iexists zero_val w64, idm
      simp only [named]
      iframe id m Hmref
      ipureintro
      refine ⟨Int.le_refl _, fun k => ?_⟩
      simp only [Int.toNat_zero, List.take_zero, List.not_mem_nil, _root_.or_false]
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
      exact ⟨by omega, union_take_step mv idm keys i key Hi Hkey Hmv⟩
    iintro HP Hv1
    iNamed HP
    rw [Int.toNat_natCast, ← Hklen, List.take_length] at Hmv
    wp_for_post
    simp only [named]
    iframe HΦ Hp
    iexists W64 1 + W64 1, _, _
    iframe i cc m Hmref Hv0
    isplitl [Hv1]
    · iright; iexact Hv1
    ipureintro; right; right; refine ⟨rfl, ?_⟩
    rw [union_done mv idm s1 keys Hkset Hmv, Hidm]
  · -- `return m`
    iapply HΦ
    iframe Hp Hv0 Hv1
    rw [Hidm, GMap.mapEmpty_union]
    iexact Hmref

end proof

end EtcdGrove
end Perennial
