/-
Compaction's `available` maps (2026-10-13, unit 5b): what `treeIndex.Keep` returns, `keep` folded
over the lock's entries (`keepFold_spec`), and the keys `treeIndex.Compact` must visit for the
map it returns (`keepAt_keys`: a key with a kept revision is in the index). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CompactIdx

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

open go_etcd_io.etcd.server.v3.storage.mvcc

section maps
variable [ext : FfiSyntax]

theorem revVal_inj' {a b : Rev} (h : revVal a = revVal b) : a = b := by
  have := congrArg revOf h
  simpa using this

/-- `availAdd`'s effect on a lookup. -/
theorem availAdd_lookup (A : GMap Revision Unit) (o : Option Rev) (r : Rev) :
    ((availAdd A o).lookup (revVal r)).isSome ↔ (A.lookup (revVal r)).isSome ∨ o = some r := by
  cases o with
  | none => simp [availAdd]
  | some r0 =>
    simp only [availAdd, GMap.lookup_insert_eq_iff, Option.some.injEq]
    by_cases h : r0 = r
    · subst h; simp
    · have h' : revVal r0 ≠ revVal r := fun e => h (revVal_inj' e)
      simp [h', h]

/-- `keep` over the entries, in order (`treeIndex.Keep`'s iteration). -/
def keepFold (A : GMap Revision Unit) (rev : w64) (L : List IdxEntry) : GMap Revision Unit :=
  L.foldl (fun A z => keepApply A rev z.2.2) A

theorem keepFold_append (A : GMap Revision Unit) (rev : w64) (L : List IdxEntry) (z : IdxEntry) :
    keepFold A rev (L ++ [z]) = keepApply (keepFold A rev L) rev z.2.2 := by
  unfold keepFold; rw [List.foldl_append]; rfl

/-- **The map `treeIndex.Keep` returns**, of the lock's entries (each key's index compacted at a
level at most `rev`): every key's `kiKeep` at `rev` of the uncompacted index. -/
theorem keepFold_spec (log : Log) (hb : LogB log) {cmax : Int} {L : List IdxEntry}
    (h : IdxCRep cmax (evsOf log) (idxOfEntries L)) (rev : w64) (hc : cmax ≤ sint.Z rev) (r : Rev) :
    ((keepFold ∅ rev L).lookup (revVal r)).isSome ↔ ∃ k, kiKeep rev (kiOfKey (evsOf log) k) = some r := by
  have hs := h.1
  have hmemL : ∀ z ∈ L, idxGet (idxOfEntries L) z.2.1 = some z.2.2 := fun z hz =>
    idxGet_of_mem _ hs (z.2.1, z.2.2) (List.mem_map_of_mem hz)
  -- the prefixes
  have key : ∀ (P S : List IdxEntry), P ++ S = L → ∀ r : Rev,
      ((keepFold ∅ rev P).lookup (revVal r)).isSome ↔ ∃ w ∈ P, kiKeep rev w.2.2 = some r := by
    intro P
    refine snoc_induction (P := fun P => ∀ S, P ++ S = L → ∀ r : Rev,
      ((keepFold ∅ rev P).lookup (revVal r)).isSome ↔ ∃ w ∈ P, kiKeep rev w.2.2 = some r) ?_ ?_ P
    · intro S _ r; simp [keepFold]
    · intro P z ih S hPS r
      have hzL : z ∈ L := by rw [← hPS]; simp
      have hPL : ∀ w ∈ P, w ∈ L := fun w hw => by rw [← hPS]; simp [hw]
      have hz := hmemL z hzL
      have hne : kiIsEmpty z.2.2 = false := by
        obtain ⟨_, _, _, _, he⟩ := h.get_some hz; exact he
      -- no earlier entry keeps what `z` makes available
      have huniq : ∀ r0, kiAvail rev z.2.2 = some r0 → ¬ ∃ w ∈ P, kiKeep rev w.2.2 = some r0 := by
        rintro r0 hr0 ⟨w, hw, hkw⟩
        have haw : kiAvail rev w.2.2 = some r0 := by
          rcases kiKeep_eq rev w.2.2 with e | e
          · rw [e] at hkw; cases hkw
          · rw [← e]; exact hkw
        have hk := h.avail_inj hb (hmemL w (hPL w hw)) hz haw hr0
        have hsort : (idxOfEntries (P ++ [z] ++ S)).Pairwise idxLess := by rw [hPS]; exact hs
        unfold idxOfEntries at hsort
        rw [List.map_append, List.map_append, List.pairwise_append, List.pairwise_append] at hsort
        have := hsort.1.2.2 _ (List.mem_map_of_mem hw) _ (List.mem_map_of_mem (List.mem_singleton_self z))
        unfold idxLess at this
        simp only at this
        rw [hk] at this
        exact goStringLt_irrefl _ this
      have ih' := ih (z :: S) (by rw [← hPS]; simp) 
      rw [keepFold_append]
      unfold keepApply
      rw [hne]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rcases kiKeep_eq rev z.2.2 with hk | hk
      · -- `keep` keeps nothing of `z`
        cases ha : kiAvail rev z.2.2 with
        | none =>
          simp only [ih' r, List.mem_append, List.mem_singleton]
          constructor
          · rintro ⟨w, hw, h'⟩; exact ⟨w, Or.inl hw, h'⟩
          · rintro ⟨w, hw | rfl, h'⟩
            · exact ⟨w, hw, h'⟩
            · rw [hk] at h'; cases h'
        | some r0 =>
          simp only [hk, reduceCtorEq, ↓reduceIte, GMap.lookup_delete_iff, GMap.lookup_insert_eq_iff]
          by_cases e : r0 = r
          · subst e
            simp only [↓reduceIte, Option.isSome_none, Bool.false_eq_true, false_iff]
            rintro ⟨w, hw, h'⟩
            rcases List.mem_append.1 hw with hw | hw
            · exact huniq r0 ha ⟨w, hw, h'⟩
            · rw [List.mem_singleton] at hw; subst hw; rw [hk] at h'; cases h'
          · have h' : revVal r0 ≠ revVal r := fun e' => e (revVal_inj' e')
            simp only [h', ↓reduceIte, ih' r, List.mem_append, List.mem_singleton]
            constructor
            · rintro ⟨w, hw, h''⟩; exact ⟨w, Or.inl hw, h''⟩
            · rintro ⟨w, hw | rfl, h''⟩
              · exact ⟨w, hw, h''⟩
              · rw [hk] at h''; cases h''
      · -- `keep` keeps what `doCompact` makes available
        cases ha : kiAvail rev z.2.2 with
        | none =>
          rw [ha] at hk
          simp only [ih' r, List.mem_append, List.mem_singleton]
          constructor
          · rintro ⟨w, hw, h'⟩; exact ⟨w, Or.inl hw, h'⟩
          · rintro ⟨w, hw | rfl, h'⟩
            · exact ⟨w, hw, h'⟩
            · rw [hk] at h'; cases h'
        | some r0 =>
          rw [ha] at hk
          simp only [hk, ↓reduceIte, GMap.lookup_insert_eq_iff]
          by_cases e : r0 = r
          · subst e
            simp only [↓reduceIte, Option.isSome_some, true_iff]
            exact ⟨z, by simp, hk⟩
          · have h' : revVal r0 ≠ revVal r := fun e' => e (revVal_inj' e')
            simp only [h', ↓reduceIte, ih' r, List.mem_append, List.mem_singleton]
            constructor
            · rintro ⟨w, hw, h''⟩; exact ⟨w, Or.inl hw, h''⟩
            · rintro ⟨w, hw | rfl, h''⟩
              · exact ⟨w, hw, h''⟩
              · rw [hk] at h''; cases h''; exact absurd rfl e
  rw [key L [] (List.append_nil L) r]
  constructor
  · rintro ⟨w, hw, h'⟩
    exact ⟨w.2.1, by rw [← h.keep_some hb rev hc (hmemL w hw)]; exact h'⟩
  · rintro ⟨k, hk⟩
    cases hg : idxGet (idxOfEntries L) k with
    | none => rw [h.keep_none hb rev hc hg] at hk; cases hk
    | some ki =>
      have hm := idxGet_some_mem hs hg
      unfold idxOfEntries at hm
      obtain ⟨w, hw, hwe⟩ := List.mem_map.1 hm
      simp only [Prod.mk.injEq] at hwe
      obtain ⟨rfl, rfl⟩ := hwe
      exact ⟨w, hw, by rw [h.keep_some hb rev hc hg]; exact hk⟩

/-- **A key with a revision compaction at `c` keeps is in the index** (of a log extending the
reader's `log₀`, its keys compacted at levels at most `c`): `treeIndex.Compact`'s clone has it. -/
theorem keepAt_keys (log₀ ilog : Log) (pend : List Change)
    (hcmp : histOf log₀ <+: histShape ilog pend ∨ histShape ilog pend <+: histOf log₀)
    (hcount : (evsOf log₀).length ≤ (evsOf (ilog ++ [pend])).length) (hb : LogB (ilog ++ [pend]))
    (hb0 : LogB log₀) {cmax : Int} {L : List IdxEntry}
    (h : IdxCRep cmax (evsOf (ilog ++ [pend])) (idxOfEntries L)) (c : Int) (hc0 : -1 ≤ c)
    (hc : cmax ≤ c) (hcl : c < log₀.length) (r : Rev) (hk : keepAt log₀ c r) :
    ∃ z ∈ L, kiAvail (W64 c) (kiOfKey (evsOf log₀) z.2.1) = some r := by
  obtain ⟨k, hk⟩ := hk
  have hlen : ilog.length < 2 ^ 63 := by have := hb.1; simp at this; omega
  have hc63 : c < 2 ^ 63 := by have := hb0.1; omega
  rw [← reader_avail log₀ ilog pend hcmp hcount hlen hb0 k c hc0 hcl] at hk
  cases hg : idxGet (idxOfEntries L) k with
  | none => rw [h.avail_none hb c hc hc63 hg] at hk; cases hk
  | some ki =>
    have hm := idxGet_some_mem h.1 hg
    unfold idxOfEntries at hm
    obtain ⟨w, hw, hwe⟩ := List.mem_map.1 hm
    simp only [Prod.mk.injEq] at hwe
    obtain ⟨hwk, -⟩ := hwe
    refine ⟨w, hw, ?_⟩
    rw [hwk, ← reader_avail log₀ ilog pend hcmp hcount hlen hb0 k c hc0 hcl]
    exact hk

end maps

end mvcc
end EtcdGrove
end Perennial
