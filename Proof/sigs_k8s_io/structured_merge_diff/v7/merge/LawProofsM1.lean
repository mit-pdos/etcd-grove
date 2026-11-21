/-
**Helpers of `merge`'s map-iterating stage proofs** (`reconcileManagedFieldsWithSchemaChanges`,
`addBackOwnedItems`, `ConflictsFromManagers`, `Updater.update`): reading an `isMF` map (its
points-to and its entries), and the pure facts on `reconcileMF` and `mfUnion` they use
(`reconcileMF_get`, `reconcileMF_sorted`, `mfUnion_nodes`).
Prove phase (2026-11-21).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.LawProofsStage
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsMF
public import Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.LawProofsIter
import all Proof.sigs_k8s_io.structured_merge_diff.v7.fieldpath.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open Iris Iris.BI Iris.ProofMode
open sigs_k8s_io.structured_merge_diff.v7

/-! ## Pure facts -/

theorem reconcileMF_get_law_holds : reconcileMF_get.law := by
  intro S t mf m
  unfold reconcileMF MF.get
  induction mf with
  | nil => simp [lookupKV]
  | cons me rest ih =>
    obtain ⟨k, e⟩ := me
    simp only [List.map_cons, lookupKV]
    by_cases h : k = m
    · simp [h]
    · simp only [h, ite_false]; exact ih

theorem reconcileMF_sorted_law_holds : reconcileMF_sorted.law := by
  intro S t mf h
  unfold reconcileMF
  rw [LawProofs.keysSorted_iff_pairwise] at h ⊢
  rw [List.pairwise_map]
  exact h.imp (fun h => h)

theorem mfUnion_mem (mf : MF) (m : GoString) (e : VSet) (h : mf.get m = some e) (q : Path)
    (hq : q ∈ e.set) : q ∈ mfUnion mf := by
  induction mf with
  | nil => simp [MF.get, lookupKV] at h
  | cons me rest ih =>
    obtain ⟨k, e'⟩ := me
    unfold mfUnion
    simp only [List.foldr_cons]
    rw [show (fun me acc => PathSet.union me.2.set acc) = fun (me : GoString × VSet) acc =>
      PathSet.union me.2.set acc from rfl]
    unfold PathSet.union
    rw [FSet_mem_union_law_holds]
    simp only [MF.get, lookupKV] at h
    by_cases hk : k = m
    · simp only [hk, ite_true, Option.some.injEq] at h
      subst h; exact Or.inl hq
    · simp only [hk, ite_false] at h
      exact Or.inr (ih h)

theorem mfUnion_nodes_law_holds : mfUnion_nodes.law := by
  intro mf m e h
  apply FSet.card_le_of_subset
  intro q hq
  unfold PathSet.nodes at hq ⊢
  rw [FSet_mem_bind_law_holds] at hq ⊢
  obtain ⟨x, hx, hqx⟩ := hq
  exact ⟨x, mfUnion_mem mf m e h x hx, hqx⟩

/-- A manager's set is small enough for `CardLt (2 ^ 63)` callees. -/
theorem mf_entry_cardLt (mf : MF) (m : GoString) (e : VSet) (h : mf.get m = some e)
    (hne : [] ∉ e.set) (hs : (mfUnion mf).nodes.card < smdSizeMax) : e.set.CardLt (2 ^ 63) :=
  nodes_cardLt _ hne (Nat.lt_of_le_of_lt (mfUnion_nodes_law_holds mf m e h) hs)

/-- A `for range` loop's visited keys, one more. -/
theorem take_dom_step {K V : Type} [DecidableEq K] (R : GMap K V) (keys : List K) (j : Int) (key : K)
    (ni : V) (hj : 0 ≤ j) (Hkey : keys[j.toNat]? = some key)
    (HR : ∀ k, (R !! k).isSome = true ↔ k ∈ keys.take j.toNat) :
    ∀ k, ((<[key := ni]> R) !! k).isSome = true ↔ k ∈ keys.take (j + 1).toNat := by
  intro k
  have Htake : keys.take (j + 1).toNat = keys.take j.toNat ++ [key] := by
    rw [show (j + 1).toNat = j.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
  rw [Htake]
  by_cases hk : key = k
  · subst hk; simp
  · rw [GMap.lookup_insert_ne _ _ hk, HR k]
    simp [List.mem_append, Ne.symm hk]

/-- The paths of the managers among `ks`. -/
def mfVis (mf : MF) (ks : List GoString) (q : Path) : Prop :=
  ∃ k ∈ ks, ∃ e, mf.get k = some e ∧ q ∈ e.set

theorem mfVis_nil (mf : MF) (q : Path) : ¬ mfVis mf [] q := by
  rintro ⟨k, hk, -⟩; simp at hk

/-- One more manager's set in a union. -/
theorem mfVis_step (mf : MF) (keys : List GoString) (j : Int) (key : GoString) (e : VSet)
    (U : PathSet) (hj : 0 ≤ j) (Hkey : keys[j.toNat]? = some key) (he : mf.get key = some e)
    (hU : ∀ q, q ∈ U ↔ mfVis mf (keys.take j.toNat) q) :
    ∀ q, q ∈ PathSet.union U e.set ↔ mfVis mf (keys.take (j + 1).toNat) q := by
  intro q
  have Htake : keys.take (j + 1).toNat = keys.take j.toNat ++ [key] := by
    rw [show (j + 1).toNat = j.toNat + 1 by omega, List.take_add_one, Hkey]; rfl
  unfold PathSet.union
  rw [FSet_mem_union_law_holds, hU, Htake]
  unfold mfVis
  constructor
  · rintro (⟨k, hk, e', he', hq⟩ | hq)
    · exact ⟨k, List.mem_append_left _ hk, e', he', hq⟩
    · exact ⟨key, by simp, e, he, hq⟩
  · rintro ⟨k, hk, e', he', hq⟩
    rcases List.mem_append.1 hk with hk | hk
    · exact Or.inl ⟨k, hk, e', he', hq⟩
    · simp at hk; subst hk; rw [he] at he'; cases he'; exact Or.inr hq

theorem mfUnion_mem_iff (mf : MF) (q : Path) : q ∈ mfUnion mf ↔ ∃ me ∈ mf, q ∈ me.2.set := by
  induction mf with
  | nil =>
    unfold mfUnion
    simp only [List.foldr_nil, List.not_mem_nil, false_and, exists_false, iff_false]
    intro h
    have := (FSet_isEmpty_iff_law_holds (PathSet.empty)).1 (by rfl) q
    exact this h
  | cons me rest ih =>
    unfold mfUnion at ih ⊢
    simp only [List.foldr_cons]
    unfold PathSet.union at ih ⊢
    rw [FSet_mem_union_law_holds, ih]
    simp

/-- Every manager visited: the union. -/
theorem mfVis_all (mf : MF) (keys : List GoString) (hs : keysSorted mf = true)
    (hk : ∀ k, k ∈ keys ↔ (mf.get k).isSome = true) :
    ∀ q, mfVis mf keys q ↔ q ∈ mfUnion mf := by
  intro q
  rw [mfUnion_mem_iff]
  constructor
  · rintro ⟨k, -, e, he, hq⟩
    exact ⟨(k, e), fpD.lookupKV_some_mem mf k e he, hq⟩
  · rintro ⟨⟨k, e⟩, hme, hq⟩
    have hget : mf.get k = some e :=
      fpD.mem_lookupKV mf k e (fpD.keysSorted_pairwise mf hs) hme
    exact ⟨k, (hk k).2 (by rw [hget]; rfl), e, hget, hq⟩

/-! ## Reading an `isMF` map -/

section iprop
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- A persistent `ManagedFields` map: its points-to and its entries' views. -/
theorem isMF_read (m : fieldpath.ManagedFields) (mf : MF) :
    isMF (GF := GF) m mf ⊢ ∃ M : GMap GoString GoInterface, m ↦$□ M ∗
      ⌜keysSorted mf = true ∧ ∀ k, (M !! k).isSome = (mf.get k).isSome⌝ ∗
      □ (∀ k i e, ⌜M !! k = some i ∧ mf.get k = some e⌝ -∗ isVSet i e) := by
  unfold isMF
  iintro ⟨%M, Hm, %h, #Hl⟩
  iexists M; iframe
  isplitr
  · ipureintro; exact h
  iapply fpL.isMFL_get M mf; iexact Hl

/-- A set is at a non-nil pointer. -/
theorem isSet_not_null (p : Loc) (S : PathSet) : isSet (GF := GF) p S ⊢ ⌜p ≠ null⌝ := by
  unfold isSet
  iintro ⟨%t, -, H⟩
  cases t with
  | mk ms cs =>
    simp only [trieRep]
    icases H with ⟨%v, %es, %ns, Hp, -⟩
    iapply typedPointsto_not_null $$ Hp

end iprop

end smd
end EtcdGrove
end Perennial
