/-
Lean-first (no Rocq counterpart).

# Lemmas of the cluster's lifecycle proofs (2026-10-29, kvreconf-final, helper LIFE)

Lists and maps: a big separating conjunction over a map as one over a list of its keys
(`bigSepM_keys`, for `all`'s range over `c.replicas`), and the list facts of a loop over a list.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.DefsCluster

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode

theorem life_drop_cons {α : Type} (l : List α) (n : Nat) (x : α) (h : l[n]? = some x) :
    l.drop n = x :: l.drop (n + 1) := by
  have hn : n < l.length := (List.getElem?_eq_some_iff.mp h).1
  rw [List.drop_eq_getElem_cons hn]
  rw [List.getElem?_eq_getElem hn] at h
  rw [Option.some.inj h]

theorem life_take_succ {α : Type} (l : List α) (n : Nat) (x : α) (h : l[n]? = some x) :
    l.take (n + 1) = l.take n ++ [x] := by
  rw [List.take_add_one, h]; rfl

section bigop
variable {GF : BundledGFunctors}

/-- A big separating conjunction over a map, as one over a list of exactly its keys. -/
theorem bigSepM_keys {V : Type} (Φ : w64 → V → IProp GF) (keys : List w64) :
    ∀ (m : GMap w64 V), keys.Nodup → (∀ k, k ∈ keys ↔ (m !! k).isSome) →
    ([∗map] k ↦ x ∈ m, Φ k x) ⊢ [∗list] k ∈ keys, ∃ x, ⌜m !! k = some x⌝ ∗ Φ k x := by
  induction keys with
  | nil =>
    intro m _ hk
    have hm : m = ∅ := by
      apply GMap.ext; intro k
      have := hk k
      simp only [List.not_mem_nil, false_iff] at this
      cases h : m !! k with
      | none => rfl
      | some _ => simp [h] at this
    subst hm
    iintro -
    iapply (BigSepL.bigSepL_nil).2; iempintro
  | cons k keys IH =>
    intro m hnd hk
    have hk0 : k ∉ keys := (List.nodup_cons.mp hnd).1
    obtain ⟨x, hx⟩ : ∃ x, m !! k = some x := by
      have := (hk k).1 List.mem_cons_self
      cases h : m !! k with
      | none => simp [h] at this
      | some x => exact ⟨x, rfl⟩
    have hk' : ∀ k', k' ∈ keys ↔ (GMap.delete k m !! k').isSome := by
      intro k'
      by_cases hkk : k = k'
      · subst hkk; simp [GMap.lookup_delete, hk0]
      · rw [GMap.lookup_delete_ne _ hkk, ← hk k']
        simp [List.mem_cons, Ne.symm hkk]
    iintro H
    ihave ⟨H1, H2⟩ := (BigSepM.bigSepM_delete (Φ := Φ) (m := m) hx).1 $$ H
    iapply (BigSepL.bigSepL_cons (Φ := fun _ k => iprop(∃ x, ⌜m !! k = some x⌝ ∗ Φ k x))).2
    isplitl [H1]
    · iexists x; iframe H1; ipureintro; exact hx
    ihave H2 := IH (GMap.delete k m) (List.nodup_cons.mp hnd).2 hk' $$ H2
    iapply (BigSepL.bigSepL_mono (Φ := fun _ k' => iprop(∃ x, ⌜GMap.delete k m !! k' = some x⌝ ∗
      Φ k' x)) ?_) $$ H2
    intro j k' hj
    have hne : k ≠ k' := fun h => hk0 (h ▸ List.mem_of_getElem? hj)
    iintro ⟨%x', %h', H⟩
    iexists x'; iframe H; ipureintro
    rw [GMap.lookup_delete_ne _ hne] at h'; exact h'

end bigop

end kvreconf
end EtcdGrove
end Perennial
