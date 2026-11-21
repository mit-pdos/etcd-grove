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
