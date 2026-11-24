/-
What a region concludes of a crash, purely (`notes/wal-fsext-i2-design.md`, §4.1-4.2): from the
consistent-cut theorem's slots (`closed_cut`) and claims whose histories are the log's
(`namesOf`), `RegionCrashed`; for a sequential region (`RegionSeq`), a prefix of its entries
(`regionCrashed_seq`). Untrusted.
-/
module

public import GooseLang.Ext.Fs.TreeSharedRes

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Classical

theorem filterMap_ite_eq {α β : Type} (l : List α) (p : α → Bool) (k : α → β) :
    l.filterMap (fun x => if p x then some (k x) else none) = (l.filter p).map k := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases h : p x
    · simp [h, ih]
    · simp [h, ih]

theorem filterMap_congr_of_mem {α β : Type} {f g : α → Option β} {l : List α}
    (h : ∀ x ∈ l, f x = g x) : l.filterMap f = l.filterMap g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.filterMap_cons, h x (List.mem_cons_self ..),
      ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem restrictN_lookup (N : NameSet) (e : Ents) (b : GoString) (hb : N.Mem b) :
    restrictN N e !! b = e !! b := by
  unfold restrictN
  rw [GMap.lookup_filter]
  cases e !! b <;> simp [hb]

/-- The entries of a claim's history, as the log has them. -/
theorem namesOf_ents (V : Hist) (j : Ino) (N : NameSet) :
    (namesOf V j N).ents = ((List.range V.2.length).filter (fun x => decide
        (∃ e, V.2[x]? = some e ∧ ∃ b, N.Mem b ∧ e.op.Writes j b))).map
      (fun x => (x, (V.2[x]?).getD ⟨.create 0 [] 0, 0⟩,
        restrictN N (entsOf (prefTree V.1 V.2 (x + 1)) j))) := by
  unfold namesOf
  simp only
  refine Eq.trans ?_ (filterMap_ite_eq _ _ _)
  apply filterMap_congr_of_mem
  intro x hx
  have hxL : x < V.2.length := List.mem_range.1 hx
  rw [List.getElem?_eq_getElem hxL]
  simp

/-- **A region's crash fact, purely**: a crash keeping the closed set `S` (with the committed
prefix `c ≥ n`) of a log whose entries began no later than they took effect, the tree left having
each slot as right after its last kept writer: every list of claims whose histories are the log's
concludes `RegionCrashed`. -/
theorem regionCrashed_of_cut {V : Hist} {S : Nat → Prop} {m' : Tree} {n c : Nat}
    (hst : Starts V.2) (hc : Closed V.2 S)
    (hcom : ∀ y, y < c → S y) (hn : n ≤ c)
    (hslot : ∀ j b, m'.entry j b = slotAfter V.1 V.2 S j b)
    (cl : List Claim) (hcl : ∀ cc ∈ cl, cc.2.2 = namesOf V cc.1 cc.2.1) :
    RegionCrashed cl n m' := by
  refine ⟨S, ?_, ?_, ?_⟩
  · intro cc hcc cc' _ x e E y e' E' hx _ hSx hy
    rw [hcl cc hcc, namesOf_ents] at hx
    obtain ⟨x0, hx0, hxe⟩ := List.mem_map.1 hx
    simp only [Prod.mk.injEq] at hxe
    obtain ⟨rfl, rfl, -⟩ := hxe
    have hxL : x0 < V.2.length := List.mem_range.1 (List.mem_filter.1 hx0).1
    refine hc x0 y hSx ⟨?_, _, List.getElem?_eq_getElem hxL, ?_⟩
    · have := hst x0 _ (List.getElem?_eq_getElem hxL)
      simp [List.getElem?_eq_getElem hxL] at hy; omega
    · simpa [List.getElem?_eq_getElem hxL] using hy
  · intro cc _ y e E _ hy; exact hcom y (by omega)
  · intro cc hcc b hb
    rw [hslot, hcl cc hcc]
    unfold NamesH.valAfter slotAfter lastKept
    rw [namesOf_ents, List.filter_map, List.getLast?_map, List.filter_filter]
    have hf : (List.range V.2.length).filter (fun x => decide (S x ∧ ∃ e, V.2[x]? = some e ∧
        e.op.Writes cc.1 b)) = (List.range V.2.length).filter (fun x =>
        ((fun xe : Nat × LogEntry × Ents => decide (S xe.1 ∧ xe.2.1.op.Writes cc.1 b)) ∘
          (fun x => (x, (V.2[x]?).getD ⟨.create 0 [] 0, 0⟩,
            restrictN cc.2.1 (entsOf (prefTree V.1 V.2 (x + 1)) cc.1)))) x &&
        decide (∃ e, V.2[x]? = some e ∧ ∃ b, cc.2.1.Mem b ∧ e.op.Writes cc.1 b)) := by
      apply List.filter_congr
      intro x hx
      have hxL : x < V.2.length := List.mem_range.1 hx
      simp only [Function.comp, List.getElem?_eq_getElem hxL, Option.getD_some, Option.some.injEq]
      by_cases h1 : S x <;> by_cases h2 : V.2[x].op.Writes cc.1 b <;> simp [h1, h2]
      exact ⟨b, hb, h2⟩
    rw [← hf]
    cases (List.filter _ (List.range V.2.length)).getLast? with
    | none => simp [namesOf, restrictN_lookup _ _ _ hb, entsOf_lookup]
    | some x => simp [restrictN_lookup _ _ _ hb, entsOf_lookup]

/-! ## A sequential region's crash keeps a prefix -/

/-- **A region whose calls are sequential**: each of its entries began after every earlier entry of
the region took effect (a single thread's calls, each begun after the previous one's entry: the
thread carries `osLogLb` from one call to the next). -/
def RegionSeq (cl : List Claim) : Prop :=
  ∀ c ∈ cl, ∀ c' ∈ cl, ∀ x e E y e' E', (x, e, E) ∈ c.2.2.ents → (y, e', E') ∈ c'.2.2.ents →
    y < x → y < e.start

/-- The least number with a property that some number has. -/
theorem exists_least (P : Nat → Prop) : ∀ N n, n ≤ N → P n → ∃ m, P m ∧ ∀ k, k < m → ¬ P k
  | 0, n, hn, hp => ⟨n, hp, fun k hk => absurd hk (by omega)⟩
  | N + 1, n, hn, hp => by
    by_cases h : ∃ k, k < n ∧ P k
    · obtain ⟨k, hk, hpk⟩ := h
      exact exists_least P N k (by omega) hpk
    · exact ⟨n, hp, fun k hk hpk => h ⟨k, hk, hpk⟩⟩

/-- **A sequential region's crash keeps a prefix of its entries** (`RegionCrashed`'s set, among the
region's entries, is all those below some `t`), with every claimed entry below the committed bound
`n`. -/
theorem regionCrashed_seq {cl : List Claim} {n : Nat} {m' : Tree} (hs : RegionSeq cl)
    (h : RegionCrashed cl n m') :
    ∃ t, (∀ c ∈ cl, ∀ y e E, (y, e, E) ∈ c.2.2.ents → y < n → y < t) ∧
      ∀ c ∈ cl, ∀ b, c.2.1.Mem b → m'.entry c.1 b = c.2.2.valAfter c.1 (· < t) b := by
  obtain ⟨K, hcl, hn, hv⟩ := h
  let idx : List Nat := cl.flatMap (fun c => c.2.2.ents.map (·.1))
  have hmem : ∀ c ∈ cl, ∀ x e E, (x, e, E) ∈ c.2.2.ents → x ∈ idx := fun c hc x e E hx =>
    List.mem_flatMap.2 ⟨c, hc, List.mem_map.2 ⟨(x, e, E), hx, rfl⟩⟩
  have hdown : ∀ x ∈ idx, ∀ y ∈ idx, K x → y < x → K y := by
    intro x hx y hy hKx hyx
    obtain ⟨c, hc, hx'⟩ := List.mem_flatMap.1 hx
    obtain ⟨⟨x0, e, E⟩, hxe, hx0⟩ := List.mem_map.1 hx'
    obtain ⟨c', hc', hy'⟩ := List.mem_flatMap.1 hy
    obtain ⟨⟨y0, e', E'⟩, hye, hy0⟩ := List.mem_map.1 hy'
    simp only at hx0 hy0
    subst hx0 hy0
    exact hcl c hc c' hc' _ e E _ e' E' hxe hye hKx (hs c hc c' hc' _ e E _ e' E' hxe hye hyx)
  obtain ⟨t, ht⟩ : ∃ t, ∀ x ∈ idx, (K x ↔ x < t) := by
    by_cases hb : ∃ z, z ∈ idx ∧ ¬ K z
    · obtain ⟨z0, hz0⟩ := hb
      obtain ⟨z, ⟨hz1, hz2⟩, hmin⟩ := exists_least (fun z => z ∈ idx ∧ ¬ K z) z0 z0 (Nat.le_refl _) hz0
      refine ⟨z, fun x hx => ⟨fun hK => ?_, fun hlt => ?_⟩⟩
      · rcases Nat.lt_or_ge x z with hlt | hge
        · exact hlt
        · rcases Nat.eq_or_lt_of_le hge with heq | hlt
          · exact absurd (heq ▸ hK) hz2
          · exact absurd (hdown x hx _ hz1 hK hlt) hz2
      · exact Classical.byContradiction fun hK => hmin x hlt ⟨hx, hK⟩
    · refine ⟨idx.sum + 1, fun x hx => ⟨fun _ => ?_, fun _ => ?_⟩⟩
      · have := le_sum_of_mem idx x hx
        omega
      · exact Classical.byContradiction fun hK => hb ⟨x, hx, hK⟩
  refine ⟨t, fun c hc y e E hy hyn => (ht y (hmem c hc y e E hy)).1 (hn c hc y e E hy hyn),
    fun c hc b hb => ?_⟩
  rw [hv c hc b hb]
  unfold NamesH.valAfter
  have hf : ∀ xe ∈ c.2.2.ents, (K xe.1 ∧ xe.2.1.op.Writes c.1 b) ↔ (xe.1 < t ∧ xe.2.1.op.Writes c.1 b) :=
    fun xe hxe => by rw [ht xe.1 (hmem c hc xe.1 xe.2.1 xe.2.2 hxe)]
  congr 2
  exact List.filter_congr (fun xe hxe => decide_eq_decide.2 (hf xe hxe))

end Fs
end Perennial

end
