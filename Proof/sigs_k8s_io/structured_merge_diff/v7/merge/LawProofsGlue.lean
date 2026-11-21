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

theorem typeAlong_none (S : Schema) : ∀ q : Path, typeAlong S none q = none
  | [] => rfl
  | _ :: q => by simp only [typeAlong, childType, Option.bind_none]; exact typeAlong_none S q

/-- Where both are defined, the type along a path (`EnsureNamedFieldsAreMembers`' descent) is
the reconciling walker's. -/
theorem typeAlong_reconAt (S : Schema) : ∀ (q : Path) (t x y : TypeRef),
    typeAlong S (some t) q = some x → reconAt S t q = some y → x = y
  | [], t, x, y, h1, h2 => by
    simp only [typeAlong, reconAt, Option.some.injEq] at h1 h2; subst h1 h2; rfl
  | pe :: q, t, x, y, h1, h2 => by
    simp only [typeAlong] at h1
    simp only [reconAt] at h2
    split at h2
    · split at h2
      · rename_i t' ht'
        cases hc : childType S (some t) pe with
        | none => rw [hc, typeAlong_none] at h1; cases h1
        | some c =>
          rw [hc] at h1
          have : c = t' := by
            unfold childType at hc
            unfold reconChild at ht'
            simp only [Option.bind_some] at hc
            split at hc
            · rename_i fs e rel n hf
              rw [hf] at ht'; simp only at ht'
              rw [ht'] at hc; cases hc; rfl
            · rename_i e rel ks k hf
              rw [hf] at ht'; simp only [Option.some.injEq] at ht' hc; subst ht' hc; rfl
            · cases hc
          subst this
          exact typeAlong_reconAt S q c x y h1 h2
      · cases h2
    · cases h2

theorem atomic_ne_granular (S : Schema) (t : TypeRef) (q : Path) (t' : TypeRef)
    (hr : reconAt S t q = some t') (ha : isAtomicT S t' = true)
    (hm : ∃ fs e rel, (typeAlong S (some t) q).bind (fun t => S.find t.name) =
      some (.map fs e rel) ∧ rel ≠ .atomic) : False := by
  obtain ⟨fs, e, rel, hf, hrel⟩ := hm
  cases hx : typeAlong S (some t) q with
  | none => rw [hx] at hf; cases hf
  | some x =>
    rw [hx] at hf
    have := typeAlong_reconAt S q t x t' hx hr
    subst this
    simp only [Option.bind_some] at hf
    unfold isAtomicT at ha
    rw [hf] at ha
    cases rel <;> simp_all

/-- Reconciling keeps `keysWithItems`. -/
theorem kwi_reconcile (S : Schema) (t : TypeRef) (s : PathSet)
    (h : keysWithItems S t s) : keysWithItems S t (reconcile S t s) := by
  -- an atomic node has a path of `s` strictly below it
  have hbelow : ∀ q, q ∈ atomicNodes S t s → ∃ r, r ≠ [] ∧ (q ++ r) ∈ s := fun q hq =>
    ((atomicNodes_mem_law_holds S t s q).1 hq).2.1
  -- no atomic node is at or below a key field (clause 3)
  have hkey : ∀ p fl n v r, (n, v) ∈ fl →
      (p ++ [.key fl, .field n] ++ r) ∉ atomicNodes S t s := by
    intro p fl n v r hn ha
    obtain ⟨r', hr', hs⟩ := hbelow _ ha
    refine (h p fl).2.2 n v (r ++ r') hn (fun h0 => hr' (List.append_eq_nil_iff.1 h0).2) ?_
    rw [← List.append_assoc]; exact hs
  -- a path of `s` not covered by an atomic node
  have hcov : ∀ q q', q ++ q' ∈ s → (¬ ∃ a, a ∈ atomicNodes S t s ∧ a <+: q ++ q') →
      ¬ ∃ a, a ∈ atomicNodes S t s ∧ a <+: q := by
    intro q q' _ hn ⟨a, ha, hp⟩
    exact hn ⟨a, ha, hp.trans (List.prefix_append q q')⟩
  intro p fl
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨n, v, hn, hm⟩
    rcases (reconcile_mem_law_holds S t s _).1 hm with ⟨hs, hnc⟩ | ha
    · apply (reconcile_mem_law_holds S t s _).2
      left
      refine ⟨(h p fl).1 ⟨n, v, hn, hs⟩, ?_⟩
      exact hcov (p ++ [.key fl]) [.field n] (by simpa using hs) (by simpa using hnc)
    · exact absurd (by simpa using ha) (hkey p fl n v [] hn)
  · intro hm hty n v hn
    rcases (reconcile_mem_law_holds S t s _).1 hm with ⟨hs, hnc⟩ | ha
    · have hs' := (h p fl).2.1 hs hty n v hn
      apply (reconcile_mem_law_holds S t s _).2
      left
      refine ⟨hs', ?_⟩
      rintro ⟨a, ha, hpre⟩
      obtain ⟨r, hr⟩ := hpre
      -- `a` is a prefix of the item, or the key field's path itself
      rcases List.eq_nil_or_concat r with rfl | ⟨r0, x, rfl⟩
      · simp only [List.append_nil] at hr; subst hr
        exact hkey p fl n v [] hn (by simpa using ha)
      · have : a ++ r0 = p ++ [.key fl] := by
          have h3 := hr
          rw [List.concat_eq_append, ← List.append_assoc,
            show p ++ [PE.key fl, PE.field n] = (p ++ [PE.key fl]) ++ [PE.field n] by simp] at h3
          exact (List.append_inj' h3 rfl).1
        exact hnc ⟨a, ha, ⟨r0, this⟩⟩
    · obtain ⟨-, -, t', hr, hat⟩ := (atomicNodes_mem_law_holds S t s _).1 ha
      exact (atomic_ne_granular S t _ t' hr hat hty).elim
  · intro n v r hn hr hm
    rcases (reconcile_mem_law_holds S t s _).1 hm with ⟨hs, -⟩ | ha
    · exact (h p fl).2.2 n v r hn hr hs
    · exact hkey p fl n v r hn ha

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
    exact ⟨hv, kwi_reconcile S t e0.set hk⟩

/-- The applier's previous entry (reconciled): at `ver`, with `keysWithItems`, small. -/
theorem apply_last (S : Schema) (t : TypeRef) (ver : GoString) (mf : MF) (mgr : GoString)
    (_hwf : S.WF) (hpre : ∀ m e, mf.get m = some e → e.version = ver ∧ keysWithItems S t e.set)
    (hsmall : (mfUnion mf).nodes.card < smdSizeMax) :
    ∀ L, (reconcileMF S t mf).get mgr = some L →
      L.version = ver ∧ keysWithItems S t L.set ∧ L.set.nodes.card < smdSizeMax := by
  intro L h
  rw [reconcileMF_get_law_holds] at h
  obtain ⟨e0, he0, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨hv, hk⟩ := hpre mgr e0 he0
  refine ⟨hv, kwi_reconcile S t e0.set hk, ?_⟩
  have h1 := reconcile_nodes_le S t e0.set
  have h2 := mfUnion_nodes_law_holds mf mgr e0 he0
  simp only
  omega

end Glue

end smd
end EtcdGrove
end Perennial
