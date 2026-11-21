/-
Lean-first (no Rocq counterpart).

What `Set.Clone.wp_proof` (batch 1 of the authorizer work) needs that lives in proof modules, which
a proof may not import (`etc/tier-check.py`): copies of `KeySet.lean`'s lemmas on `insertAll` and
of `Set.Insert.wp_proof`; and that a set's keys are the set.
-/
module

public import Spec.k8s_io.apimachinery.pkg.util.sets.Set__Insert
public import Spec.k8s_io.apimachinery.pkg.util.sets.KeySet

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace sets

open Iris Iris.BI Iris.ProofMode k8s_io.apimachinery.pkg.util.sets

section pure
variable [GooseExts]

theorem lookup_insertAll_b1 {K : Type} [DecidableEq K] (s : GMap K Elem) (ks : List K) (k : K) :
    insertAll s ks !! k = if k ∈ ks then some present else s !! k := by
  induction ks generalizing s with
  | nil => simp
  | cons a ks ih =>
    rw [insertAll_cons, ih]
    by_cases h : k ∈ ks
    · simp [h]
    · by_cases ha : a = k
      · subst ha; simp
      · simp [h, ha, Ne.symm ha]

theorem insertAll_keys_b1 {K V : Type} [DecidableEq K] (m : GMap K V) (keys : List K)
    (h : ∀ k, k ∈ keys ↔ (m !! k).isSome) : insertAll ∅ keys = keysOf m := by
  ext k
  rw [lookup_insertAll_b1]
  unfold keysOf
  rw [GMap.lookup_fmap]
  by_cases hk : k ∈ keys
  · have := (h k).1 hk
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 this
    simp [hk, hv]
  · have : (m !! k) = none := by
      cases hm : m !! k with
      | none => rfl
      | some v => exact absurd ((h k).2 (by rw [hm]; rfl)) hk
    simp [hk, this]

/-- A set's keys are the set. -/
theorem keysOf_set_b1 {K : Type} [DecidableEq K] (s : GMap K Elem) : keysOf s = s := by
  ext k
  unfold keysOf
  rw [GMap.lookup_fmap]
  cases s !! k <;> rfl

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.util.sets.Assumptions]

/-- `Set[T].Insert`: a copy of `Set.Insert.wp_proof` (`Set__Insert.lean`, a proof module, which a
proof may not import), for `Set.Clone.wp_proof`, whose statement has no callee hypothesis. -/
theorem Set.wp_Insert_b1 : Set.Insert.spec (GF := GF) (hG := hG) := by
  intro K _ _ _ _ T _ _ m s sl dq ks
  wp_start as ⟨Hm, Hsl⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  ihave IH : iprop(∃ (n : w64) (x : K),
      "i" ∷ i_ptr ↦ n ∗
      "item" ∷ item_ptr ↦ x ∗
      "Hm" ∷ m ↦$ insertAll s (ks.take (sint.nat n)) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ ks.length⌝) $$ [i item Hm]
  · iexists W64 0, _
    iframe
    ipureintro
    exact ⟨by decide, by simp⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ks.length := by word
    obtain ⟨e, He⟩ : ∃ e, ks[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len from ⟨Hn.1, Hif⟩, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) ks dq e Hn.1 $$ [Hsl] as Hsl
    · iframe; ipureintro; exact He
    wp_apply wp_mapInsert $$ Hm as Hm
    wp_for_post
    iframe
    iexists n + W64 1, e
    iframe
    have Htake : ks.take (sint.nat (n + W64 1)) = ks.take (sint.nat n) ++ [e] := by
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word]
      rw [List.take_add_one, He]; rfl
    rw [Htake, insertAll_append]
    iframe
    ipureintro
    constructor <;> word
  · rw [show sint.nat n = ks.length by word, List.take_length]
    iapply HΦ
    iframe

end proof

end sets
end EtcdGrove
end Perennial
