/-
**The pure facts of `Updater.Apply`'s glue** (`merge/Updater__Apply.lean`): `prune`'s and
`update`'s premises from `Apply`'s (the one-version and `keysWithItems` premise on the managers,
D9's `inputsSmall`, the objects' conformance).
Prove phase (2026-11-21).
-/
module

public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.LawProofs
public import Proof.sigs_k8s_io.structured_merge_diff.v7.merge.LawProofsM1

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace smd

open sigs_k8s_io.structured_merge_diff.v7

namespace Glue

/-! ## Trie nodes -/

theorem mem_nePrefixes_append {q p : Path} (r : Path) (h : q ∈ Path.nePrefixes p) :
    q ∈ Path.nePrefixes (p ++ r) := by
  unfold Path.nePrefixes at h ⊢
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 h
  rw [List.mem_range] at hk
  refine List.mem_map.2 ⟨k, ?_, ?_⟩
  · rw [List.mem_range, List.length_append]; omega
  · rw [List.take_append_of_le_length (by omega)]

/-- Reconciling adds no trie node (its paths are the set's, or prefixes of them). -/
theorem reconcile_nodes_sub (S : Schema) (t : TypeRef) (s : PathSet) (q : Path)
    (hq : q ∈ (reconcile S t s).nodes) : q ∈ s.nodes := by
  unfold PathSet.nodes at hq ⊢
  rw [FSet_mem_bind_law_holds] at hq ⊢
  obtain ⟨x, hx, hqx⟩ := hq
  rcases (reconcile_mem_law_holds S t s x).1 hx with ⟨hxs, -⟩ | hxa
  · exact ⟨x, hxs, hqx⟩
  · obtain ⟨-, ⟨r, -, hr⟩, -⟩ := (atomicNodes_mem_law_holds S t s x).1 hxa
    exact ⟨x ++ r, hr, mem_nePrefixes_append r hqx⟩

theorem reconcile_nodes_le (S : Schema) (t : TypeRef) (s : PathSet) :
    (reconcile S t s).nodes.card ≤ s.nodes.card :=
  FSet.card_le_of_subset _ _ (reconcile_nodes_sub S t s)

/-! ## `keysWithItems` of the sets `Apply` hands to `prune` -/

/-- Reconciling keeps `keysWithItems`. -/
theorem kwi_reconcile (S : Schema) (t : TypeRef) (s : PathSet) (hwf : S.WF)
    (h : keysWithItems S t s) : keysWithItems S t (reconcile S t s) := by
  sorry

/-- A conforming value's field set has `keysWithItems`. -/
theorem kwi_fieldSet (S : Schema) (t : TypeRef) (x : UVal) (hwf : S.WF) (hc : conforms S t x) :
    keysWithItems S t (fieldSet S t x) := by
  sorry

/-! ## Sizes -/

/-- Merging two conforming values adds no node beyond the two sides' (`merge_size`, with the
conformance premise `Apply` has). -/
theorem merge_size_conf (S : Schema) (t : TypeRef) (l r : UVal) (hwf : S.WF)
    (hl : conforms S t l) (hr : conforms S t r) : (merge S t l r).size ≤ l.size + r.size := by
  sorry

/-- Pruning adds no node (`prune_size`, from `removeItems_size`). -/
theorem prune_size_le (S : Schema) (t : TypeRef) (merged : UVal) (mf : MF) (last : Option VSet) :
    (prune S t merged mf last).size ≤ merged.size := by
  unfold prune
  split
  · exact Nat.le_refl _
  · split
    · exact Nat.le_refl _
    · exact removeItems_size_law_holds S t merged _

/-! ## `Apply`'s premises of `prune` -/

/-- The applier's new managers (`mf0` with its entry `⟨fieldSet config, ver, true⟩`): every
entry at `ver`, with `keysWithItems`. -/
theorem apply_mf1_entries (S : Schema) (t : TypeRef) (config : UVal) (ver : GoString) (mf : MF)
    (mgr : GoString) (hwf : S.WF) (hc : conforms S t config)
    (hpre : ∀ m e, mf.get m = some e → e.version = ver ∧ keysWithItems S t e.set) :
    ∀ m e, ((reconcileMF S t mf).set mgr ⟨fieldSet S t config, ver, true⟩).get m = some e →
      e.version = ver ∧ keysWithItems S t e.set := by
  intro m e h
  rw [MF.get_set_law_holds] at h
  split at h
  · cases h; exact ⟨rfl, kwi_fieldSet S t config hwf hc⟩
  · rw [reconcileMF_get_law_holds] at h
    obtain ⟨e0, he0, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨hv, hk⟩ := hpre m e0 he0
    exact ⟨hv, kwi_reconcile S t e0.set hwf hk⟩

/-- The applier's previous entry (reconciled): at `ver`, with `keysWithItems`, small. -/
theorem apply_last (S : Schema) (t : TypeRef) (ver : GoString) (mf : MF) (mgr : GoString)
    (hwf : S.WF) (hpre : ∀ m e, mf.get m = some e → e.version = ver ∧ keysWithItems S t e.set)
    (hsmall : (mfUnion mf).nodes.card < smdSizeMax) :
    ∀ L, (reconcileMF S t mf).get mgr = some L →
      L.version = ver ∧ keysWithItems S t L.set ∧ L.set.nodes.card < smdSizeMax := by
  intro L h
  rw [reconcileMF_get_law_holds] at h
  obtain ⟨e0, he0, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨hv, hk⟩ := hpre mgr e0 he0
  refine ⟨hv, kwi_reconcile S t e0.set hwf hk, ?_⟩
  have h1 := reconcile_nodes_le S t e0.set
  have h2 := mfUnion_nodes_law_holds mf mgr e0 he0
  simp only
  omega

end Glue

end smd
end EtcdGrove
end Perennial
