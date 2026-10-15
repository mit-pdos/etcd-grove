/-
Compaction of the index, the pure lemmas the proofs of `treeIndex.Compact`/`Keep` and
`keyIndex.compact`/`keep` use (2026-10-13, unit 5b; `Compact.lean` for the model): what a reader
of the index's history finds compaction keeps (`reader_avail`, `reader_keep`), `kiKeep` under
compaction (`kiKeep_kiCompact_S`), the generations `doCompact` walks after a compaction
(`kiCompact_gensOk`), the revisions compaction keeps belong to their key (`IdxCRep.avail_inj`),
and a compaction step of one key of the index (`IdxCRep.compactAt`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Compact

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-! ### `kiKeep`, generation by generation -/

/-- `kiKeep`'s choice in the generation `g` `doCompact` found, `last` whether it is the last one. -/
def keepOf (c : w64) (g : Gen) (last : Prop) [Decidable last] : Option Rev :=
  let ri := genWalk g.revs (pAbove c)
  if ri = -1 then none
  else if g.revs ≠ [] ∧ ri = ((g.revs.length - 1 : Nat) : Int) ∧ ¬ last then none
  else some (g.revs.getD ri.toNat Rev.zero)

theorem keepOf_congr (c : w64) (g : Gen) (l l' : Prop) [Decidable l] [Decidable l'] (h : l ↔ l') :
    keepOf c g l = keepOf c g l' := by
  unfold keepOf; simp only [h]

/-- Lastness does not matter unless the walk stops at the generation's last revision. -/
theorem keepOf_last_irrel (c : w64) (g : Gen) (l l' : Prop) [Decidable l] [Decidable l']
    (h : genWalk g.revs (pAbove c) ≠ ((g.revs.length - 1 : Nat) : Int)) :
    keepOf c g l = keepOf c g l' := by
  unfold keepOf; simp only [h, false_and, and_false, ↓reduceIte]

theorem kiKeep_keepOf (c : w64) (ki : KeyIndex) :
    kiKeep c ki = keepOf c (ki.gens.getD (compactGenIdx c ki.gens) Gen.empty)
      (compactGenIdx c ki.gens = ki.gens.length - 1) := by
  unfold kiKeep
  split
  · rename_i he
    unfold kiIsEmpty at he
    split at he
    · rename_i g hg
      simp only [decide_eq_true_eq] at he
      simp only [hg, compactGenIdx, List.getD_cons_zero]
      unfold keepOf
      simp only [he]
      rw [genWalk_eq_none (by simp)]
      rfl
    · cases he
  · rfl

/-- `keepOf` on the cut generation (cut at `c ≤ c'`). -/
theorem keepOf_cutGen (c c' : w64) (hcc : sint.Z c ≤ sint.Z c') (g : Gen) (l : Prop) [Decidable l] :
    keepOf c' (cutGen c g) l = keepOf c' g l := by
  rcases cutGen_cases c g with h | ⟨j, hj, -, hm, hr, -⟩
  · rw [h]
  · have hw' : (j : Int) ≤ genWalk g.revs (pAbove c') := genWalk_ge hj (by simp [pAbove]; omega)
    have hwr := genWalk_range g.revs (pAbove c')
    unfold keepOf
    simp only []
    rw [hr, genWalk_drop hw']
    generalize hW : genWalk g.revs (pAbove c') = W at *
    have hne : g.revs.drop j ≠ [] := by
      intro h; have := congrArg List.length h; simp at this; omega
    have hne' : g.revs ≠ [] := by intro h; rw [h] at hj; simp at hj
    have h1 : W - j ≠ -1 := by omega
    have h2 : W ≠ -1 := by omega
    simp only [h1, h2, ↓reduceIte, ne_eq, hne, hne', not_false_eq_true, true_and, List.length_drop]
    have hget : (g.revs.drop j).getD (W - j).toNat Rev.zero = g.revs.getD W.toNat Rev.zero := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
      congr 2; omega
    rw [hget]
    by_cases hl : W = ((g.revs.length - 1 : Nat) : Int)
    · have : W - j = ((g.revs.length - j - 1 : Nat) : Int) := by omega
      rw [this]; simp only [hl, true_and]
    · have : W - j ≠ ((g.revs.length - j - 1 : Nat) : Int) := by omega
      simp only [hl, this, false_and, ↓reduceIte]

/-- A revision above `c` appended to the last generation does not change `keepOf`. -/
theorem keepOf_genPut_last (c : w64) (g : Gen) (rev : Rev) (hc : sint.Z c < sint.Z rev.main)
    (l : Prop) [Decidable l] (hl : l) : keepOf c (genPut g rev) l = keepOf c g l := by
  unfold keepOf
  simp only []
  rw [genPut_revs, genWalk_append_true _ _ _ (by simp [pAbove]; omega)]
  have hwr := genWalk_range g.revs (pAbove c)
  generalize genWalk g.revs (pAbove c) = W at *
  simp only [hl, not_true_eq_false, and_false, ↓reduceIte]
  split
  · rfl
  · congr 1
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega)]

theorem kiKeep_kiPut {ki : KeyIndex} (hwf : KiWf ki) (c : w64) (rev : Rev)
    (hc : sint.Z c < sint.Z rev.main) : kiKeep c (kiPut ki rev) = kiKeep c ki := by
  have hne := hwf.ne
  have hlt := compactGenIdx_lt c ki.gens hne
  rw [kiKeep_keepOf, kiKeep_keepOf, kiPut_gens_of_ne hne, compactGenIdx_put hwf,
    length_dropLast_append _ _ hne]
  by_cases hl : compactGenIdx c ki.gens + 1 = ki.gens.length
  · rw [show compactGenIdx c ki.gens = ki.gens.length - 1 by omega, getD_dropLast_append_last _ _ _ hne,
      getLastD_eq_getD _ _ hne]
    exact keepOf_genPut_last c _ rev hc _ rfl
  · rw [getD_dropLast_append_lt _ _ _ _ (by omega)]

theorem kiKeep_kiTombstone {ki : KeyIndex} (hwf : KiWf ki) (c : w64) (rev : Rev)
    (hc : sint.Z c < sint.Z rev.main) : kiKeep c (kiTombstone ki rev) = kiKeep c ki := by
  rw [← kiKeep_kiPut hwf c rev hc]
  have hne := hwf.ne
  have hput := hwf.put rev
  have hlast : ¬ tombZ ((kiPut ki rev).gens.getLastD Gen.empty) < sint.Z c := by
    rw [kiPut_gens_of_ne hwf.ne, getLastD_append_singleton]
    unfold tombZ
    rw [genPut_revs, List.getLastD_eq_getLast?, List.getLast?_append, List.getLast?_singleton]
    all_goals first | omega | (simp; omega) | simp
  have hlt := compactGenIdx_lt c (kiPut ki rev).gens hput.ne
  rw [kiKeep_keepOf, kiKeep_keepOf, kiTombstone_gens, compactGenIdx_appendEmpty hput.ne c hlast,
    getD_append_lt _ _ _ _ hlt]
  by_cases hl : compactGenIdx c (kiPut ki rev).gens = (kiPut ki rev).gens.length - 1
  · apply keepOf_last_irrel
    have hlen := length_dropLast_append ki.gens (genPut (ki.gens.getLastD Gen.empty) rev) hne
    rw [hl, kiPut_gens_of_ne hne, hlen, getD_dropLast_append_last _ _ _ hne, genPut_revs,
      genWalk_append_true _ _ _ (by simp [pAbove]; omega)]
    have := genWalk_range (ki.gens.getLastD Gen.empty).revs (pAbove c)
    simp only [List.length_append, List.length_singleton]
    omega
  · apply keepOf_congr
    simp only [List.length_append, List.length_singleton]
    omega

theorem kiKeep_kiApply {ki : KeyIndex} (hwf : KiWf ki) (c : w64) (e : Ev)
    (hc : sint.Z c < sint.Z e.rev.main) : kiKeep c (kiApply ki e) = kiKeep c ki := by
  unfold kiApply
  split
  · split
    · rfl
    · exact kiKeep_kiTombstone hwf c _ hc
  · exact kiKeep_kiPut hwf c _ hc

theorem kiKeep_fold (c : w64) (k : GoString) : ∀ (B : List Ev) (ki : KeyIndex), KiWf ki →
    (∀ e ∈ B, sint.Z c < sint.Z e.rev.main) → kiKeep c (kiFold ki B k) = kiKeep c ki
  | [], _, _, _ => rfl
  | e :: B, ki, hwf, hB => by
    rw [kiFold_cons]
    have hB' : ∀ x ∈ B, sint.Z c < sint.Z x.rev.main := fun x hx => hB x (List.mem_cons_of_mem _ hx)
    split
    · rw [kiKeep_fold c k B _ (kiApply_wf hwf e) hB', kiKeep_kiApply hwf c e (hB e List.mem_cons_self)]
    · exact kiKeep_fold c k B ki hwf hB'

/-! ### A reader's history: the certified log's events, then later ones -/

/-- A reader's history is the certified log's events followed by events of later revisions. -/
theorem reader_prefix_from (log₀ ilog : Log) (pend : List Change)
    (hcmp : histOf log₀ <+: histShape ilog pend ∨ histShape ilog pend <+: histOf log₀)
    (hcount : (evsOf log₀).length ≤ (evsOf (ilog ++ [pend])).length) (hlen : ilog.length < 2 ^ 63) :
    ∃ rest, evsOf (ilog ++ [pend]) = evsOf log₀ ++ rest ∧
      ∀ e ∈ rest, (log₀.length : Int) ≤ sint.Z e.rev.main := by
  rcases hcmp with hpre | hpre
  · obtain ⟨rest, h, hfrom, -⟩ := histOf_prefix_shape log₀ ilog pend hpre hlen
    refine ⟨rest, h, fun e he => ?_⟩
    have h1 := hfrom.ge e he
    have h2 := hfrom.lt e he
    have : sint.Z e.rev.main = (e.rev.main.toNat : Int) := by word
    omega
  · have := evsOfHist_prefix_of_count _ _ hpre (by rw [evsOfHist_histShape]; exact hcount)
    rw [evsOfHist_histShape] at this
    exact ⟨[], by rw [this, List.append_nil], fun e he => by simp at he⟩

/-- **What compaction at `c` keeps, as a reader finds it**: the certified log's choice. -/
theorem reader_avail (log₀ ilog : Log) (pend : List Change)
    (hcmp : histOf log₀ <+: histShape ilog pend ∨ histShape ilog pend <+: histOf log₀)
    (hcount : (evsOf log₀).length ≤ (evsOf (ilog ++ [pend])).length) (hlen : ilog.length < 2 ^ 63)
    (hb0 : LogB log₀) (k : GoString) (c : Int) (hc0 : -1 ≤ c) (hc : c < log₀.length) :
    kiAvail (W64 c) (kiOfKey (evsOf (ilog ++ [pend])) k) = kiAvail (W64 c) (kiOfKey (evsOf log₀) k) := by
  obtain ⟨rest, hrest, hfrom⟩ := reader_prefix_from log₀ ilog pend hcmp hcount hlen
  rw [hrest, kiOfKey_eq_kiFold, kiFold_append, ← kiOfKey_eq_kiFold]
  apply kiAvail_fold _ k _ _ (kiOfKey_struct k _).1
  intro e he
  have := hfrom e he
  have hl := hb0.1
  have : sint.Z (W64 c) = c := by word
  omega

/-- **What `keep` keeps at `rev`, as a reader finds it**: the certified log's choice. -/
theorem reader_keep (log₀ ilog : Log) (pend : List Change)
    (hcmp : histOf log₀ <+: histShape ilog pend ∨ histShape ilog pend <+: histOf log₀)
    (hcount : (evsOf log₀).length ≤ (evsOf (ilog ++ [pend])).length) (hlen : ilog.length < 2 ^ 63)
    (hb0 : LogB log₀) (k : GoString) (rev : w64) (h0 : 0 ≤ sint.Z rev) (hrev : sint.Z rev < log₀.length) :
    kiKeep rev (kiOfKey (evsOf (ilog ++ [pend])) k) = kiKeep rev (kiOfKey (evsOf log₀) k) := by
  obtain ⟨rest, hrest, hfrom⟩ := reader_prefix_from log₀ ilog pend hcmp hcount hlen
  rw [hrest, kiOfKey_eq_kiFold, kiFold_append, ← kiOfKey_eq_kiFold]
  apply kiKeep_fold _ k _ _ (kiOfKey_struct k _).1
  intro e he
  have := hfrom e he
  omega

/-! ### `kiKeep` and `kiAvail` -/

/-- `keep`'s revision is `doCompact`'s, or none. -/
theorem kiKeep_eq (c : w64) (ki : KeyIndex) : kiKeep c ki = none ∨ kiKeep c ki = kiAvail c ki := by
  unfold kiKeep kiAvail
  simp only []
  split
  · left; rfl
  · split
    · left; rfl
    · split
      · left; rfl
      · right; rfl

/-- An empty key index keeps nothing. -/
theorem kiAvail_isEmpty {ki : KeyIndex} (h : kiIsEmpty ki = true) (c : w64) : kiAvail c ki = none := by
  unfold kiIsEmpty at h
  unfold kiAvail
  split at h
  · rename_i g hg
    simp only [decide_eq_true_eq] at h
    simp only [hg, compactGenIdx, List.getD_cons_zero, h]
    rw [genWalk_eq_none (by simp)]
    rfl
  · cases h

/-- An earlier compaction of a key index does not change what `keep` keeps later. -/
theorem kiKeep_kiCompact_S {ki : KeyIndex} (hwf : KiWf ki) (c c' : w64) (hcc : sint.Z c ≤ sint.Z c') :
    kiKeep c' (kiCompact c ki) = kiKeep c' ki := by
  obtain ⟨hge, hidx⟩ := compactGenIdx_compact_ge hwf c c' hcc
  have hlt := compactGenIdx_lt c ki.gens hwf.ne
  have hlt' := compactGenIdx_lt c' ki.gens hwf.ne
  rw [kiKeep_keepOf, kiKeep_keepOf, hidx, kiCompact_gens c ki, dropSet_length]
  generalize compactGenIdx c ki.gens = gi at *
  generalize compactGenIdx c' ki.gens = m at *
  rcases Nat.lt_or_eq_of_le hge with hgt | heq
  · rw [show m - gi = (m - gi - 1) + 1 by omega, dropSet_getDs, show gi + (m - gi - 1) + 1 = m by omega]
    apply keepOf_congr; omega
  · subst heq
    rw [Nat.sub_self, dropSet_getD0 _ _ _ _ hlt, keepOf_cutGen c c' hcc]
    apply keepOf_congr; omega

/-- A compacted key index has generations as `doCompact` walks them: some, every one but the last
with a revision (`InvCompact.lean`'s `gensOk`). -/
theorem kiCompact_gensOk {ki : KeyIndex} (hwf : KiWf ki) (c : w64) :
    (kiCompact c ki).gens ≠ [] ∧
      ∀ i, i + 1 < (kiCompact c ki).gens.length → ((kiCompact c ki).gens.getD i Gen.empty).revs ≠ [] := by
  have hlt := compactGenIdx_lt c ki.gens hwf.ne
  have hG := kiCompact_gens c ki
  refine ⟨?_, ?_⟩
  · intro h
    have := congrArg List.length h
    rw [hG, dropSet_length] at this
    simp at this
    omega
  · intro i hi
    rw [hG] at hi ⊢
    rw [dropSet_length] at hi
    cases i with
    | zero =>
      rw [dropSet_getD0 _ _ _ _ hlt]
      intro h
      rw [cutGen_revs_ne] at h
      exact hwf.nonlast _ (by omega) h
    | succ j =>
      rw [dropSet_getDs]
      exact hwf.nonlast _ (by omega)

/-! ### Revisions of a key index -/

/-- The revision compaction keeps is one of the key index's. -/
theorem kiAvail_mem {c : w64} {ki : KeyIndex} {r : Rev} (h : kiAvail c ki = some r) : r ∈ kiRevs ki := by
  unfold kiAvail at h
  simp only [] at h
  split at h
  · cases h
  · rename_i hw
    simp only [Option.some.injEq] at h
    subst h
    generalize hg : ki.gens.getD (compactGenIdx c ki.gens) Gen.empty = g at *
    have hr := genWalk_range g.revs (pAbove c)
    have hlt : (genWalk g.revs (pAbove c)).toNat < g.revs.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    simp only [Option.getD_some]
    have hgm : g ∈ ki.gens := by
      rw [List.getD_eq_getElem?_getD] at hg
      cases hx : ki.gens[compactGenIdx c ki.gens]? with
      | none =>
        rw [hx] at hg; simp only [Option.getD_none] at hg; subst hg
        simp [Gen.empty] at hlt
      | some x =>
        rw [hx] at hg; simp only [Option.getD_some] at hg; subst hg
        exact List.mem_of_getElem? hx
    exact kiRevs_mem hgm (List.getElem_mem hlt)

/-- Compaction drops revisions, adds none. -/
theorem kiRevs_kiCompact {c : w64} {ki : KeyIndex} {r : Rev} (h : r ∈ kiRevs (kiCompact c ki)) :
    r ∈ kiRevs ki := by
  unfold kiRevs at h
  rw [List.mem_flatten] at h
  obtain ⟨rs, hrs, hr⟩ := h
  rw [List.mem_map] at hrs
  obtain ⟨g', hg', rfl⟩ := hrs
  rw [kiCompact_gens] at hg'
  have hg'' := List.mem_of_mem_drop hg'
  rcases List.mem_or_eq_of_mem_set hg'' with hm | he
  · exact kiRevs_mem hm hr
  · subst he
    generalize hg : ki.gens.getD (compactGenIdx c ki.gens) Gen.empty = g at *
    have hr' : r ∈ g.revs := by
      rcases cutGen_cases c g with h | ⟨j, -, -, -, h, -⟩
      · rw [h] at hr; exact hr
      · rw [h] at hr; exact List.mem_of_mem_drop hr
    rw [List.getD_eq_getElem?_getD] at hg
    cases hx : ki.gens[compactGenIdx c ki.gens]? with
    | none =>
      rw [hx] at hg; simp only [Option.getD_none] at hg; subst hg
      simp [Gen.empty] at hr'
    | some x =>
      rw [hx] at hg; simp only [Option.getD_some] at hg; subst hg
      exact kiRevs_mem (List.mem_of_getElem? hx) hr'

/-- A revision of a key's index is the revision of an event of that key. -/
theorem kiRevs_kiOfKey {evs : List Ev} {k : GoString} {r : Rev} (h : r ∈ kiRevs (kiOfKey evs k)) :
    ∃ e ∈ evs, e.rev = r ∧ e.key = k := by
  have hev := (kiOfKey_struct k evs).2.2
  unfold kiRevs at h
  rw [List.mem_flatten] at h
  obtain ⟨rs, hrs, hr⟩ := h
  rw [List.mem_map] at hrs
  obtain ⟨g, hg, rfl⟩ := hrs
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hr
  obtain ⟨e, he, h1, h2, -⟩ := hev i p g r hi hp
  exact ⟨e, he, h1, h2⟩

/-- Two events of a log with one revision are one event. -/
theorem evsOf_rev_inj (log : Log) (hb : LogB log) {e1 e2 : Ev} (h1 : e1 ∈ evsOf log)
    (h2 : e2 ∈ evsOf log) (h : e1.rev = e2.rev) : e1 = e2 := by
  have hord := (evsOf_ord log hb).1
  rw [List.pairwise_map, List.pairwise_iff_getElem] at hord
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h1
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem h2
  have hirr : ∀ a : Rev, ¬ Rev.lt a a := by
    intro a ha; rcases ha with ha | ⟨-, ha⟩ <;> omega
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · exact absurd (h ▸ hord i j hi hj hij) (hirr _)
  · rfl
  · exact absurd (h ▸ hord j i hj hi hij) (hirr _)

/-! ### The index -/

/-- On a sorted index, a key absent from the members has no entry. -/
theorem idxGet_none_of_not_mem {idx : IndexM} (hs : idx.Pairwise idxLess) {k : GoString}
    (h : ∀ v, (k, v) ∉ idx) : idxGet idx k = none := by
  cases hg : idxGet idx k with
  | none => rfl
  | some v => exact absurd (idxGet_some_mem hs hg) (h v)

/-- Two sorted indexes with the same members of key `k'` agree at `k'`. -/
theorem idxGet_congr {idx idx' : IndexM} (hs : idx.Pairwise idxLess) (hs' : idx'.Pairwise idxLess)
    {k' : GoString} (h : ∀ v, (k', v) ∈ idx' ↔ (k', v) ∈ idx) : idxGet idx' k' = idxGet idx k' := by
  cases hg : idxGet idx k' with
  | none =>
    apply idxGet_none_of_not_mem hs'
    intro v hv
    have := idxGet_of_mem idx hs _ ((h v).1 hv)
    rw [hg] at this; cases this
  | some v => exact idxGet_of_mem idx' hs' (k', v) ((h v).2 (idxGet_some_mem hs hg))

/-- A sorted index has one entry per key. -/
theorem idx_key_unique {idx : IndexM} (hs : idx.Pairwise idxLess) {i j : Nat} {a b : GoString × KeyIndex}
    (hi : idx[i]? = some a) (hj : idx[j]? = some b) (hk : a.1 = b.1) : i = j := by
  rw [List.pairwise_iff_getElem] at hs
  obtain ⟨hil, rfl⟩ := List.getElem?_eq_some_iff.1 hi
  obtain ⟨hjl, rfl⟩ := List.getElem?_eq_some_iff.1 hj
  rcases Nat.lt_trichotomy i j with h | h | h
  · have := hs i j hil hjl h; unfold idxLess at this; rw [hk] at this
    exact absurd this (goStringLt_irrefl _)
  · exact h
  · have := hs j i hjl hil h; unfold idxLess at this; rw [hk] at this
    exact absurd this (goStringLt_irrefl _)

/-- A key the index has: its generations as `doCompact` walks them. -/
theorem IdxCRep.gensOk {cmax : Int} {log : Log} (hb : LogB log) {idx : IndexM}
    (h : IdxCRep cmax (evsOf log) idx) (hc0 : cmax < 2 ^ 63) {k : GoString} {ki : KeyIndex}
    (hg : idxGet idx k = some ki) :
    ki.gens ≠ [] ∧ ∀ i, i + 1 < ki.gens.length → (ki.gens.getD i Gen.empty).revs ≠ [] := by
  obtain ⟨c, -, -, rfl, -⟩ := h.get_some hg
  exact kiCompact_gensOk (kiOfKey_KiS log hb k).wf _

/-- A key the index has: compaction at `c ≥ cmax` keeps of it what it keeps of the uncompacted one. -/
theorem IdxCRep.avail_some {cmax : Int} {log : Log} (hb : LogB log) {idx : IndexM}
    (h : IdxCRep cmax (evsOf log) idx) (c : Int) (hc : cmax ≤ c) (hc' : c < 2 ^ 63)
    {k : GoString} {ki : KeyIndex} (hg : idxGet idx k = some ki) :
    kiAvail (W64 c) ki = kiAvail (W64 c) (kiOfKey (evsOf log) k) := by
  obtain ⟨c0, h0, h1, rfl, -⟩ := h.get_some hg
  exact kiAvail_kiCompact log hb k c0 c h0 (by omega) hc'

/-- A key the index does not have: compaction at `c ≥ cmax` keeps nothing of it. -/
theorem IdxCRep.avail_none {cmax : Int} {log : Log} (hb : LogB log) {idx : IndexM}
    (h : IdxCRep cmax (evsOf log) idx) (c : Int) (hc : cmax ≤ c) (hc' : c < 2 ^ 63)
    {k : GoString} (hg : idxGet idx k = none) :
    kiAvail (W64 c) (kiOfKey (evsOf log) k) = none := by
  obtain ⟨c0, h0, h1, he⟩ := h.get_none hg
  rw [← kiAvail_kiCompact log hb k c0 c h0 (by omega) hc']
  exact kiAvail_isEmpty he _

/-- A key the index has: `keep` at `rev ≥ cmax` keeps of it what it keeps of the uncompacted one. -/
theorem IdxCRep.keep_some {cmax : Int} {log : Log} (hb : LogB log) {idx : IndexM}
    (h : IdxCRep cmax (evsOf log) idx) (rev : w64) (hc : cmax ≤ sint.Z rev)
    {k : GoString} {ki : KeyIndex} (hg : idxGet idx k = some ki) :
    kiKeep rev ki = kiKeep rev (kiOfKey (evsOf log) k) := by
  obtain ⟨c0, h0, h1, rfl, -⟩ := h.get_some hg
  apply kiKeep_kiCompact_S (kiOfKey_KiS log hb k).wf
  have : sint.Z rev < 2 ^ 63 := by word
  have : sint.Z (W64 c0) = c0 := by word
  omega

/-- A key the index does not have: `keep` at `rev ≥ cmax` keeps nothing of it. -/
theorem IdxCRep.keep_none {cmax : Int} {log : Log} (hb : LogB log) {idx : IndexM}
    (h : IdxCRep cmax (evsOf log) idx) (rev : w64) (hc : cmax ≤ sint.Z rev)
    {k : GoString} (hg : idxGet idx k = none) :
    kiKeep rev (kiOfKey (evsOf log) k) = none := by
  obtain ⟨c0, h0, h1, he⟩ := h.get_none hg
  have : sint.Z rev < 2 ^ 63 := by word
  have hz : sint.Z (W64 c0) = c0 := by word
  rw [← kiKeep_kiCompact_S (kiOfKey_KiS log hb k).wf (W64 c0) rev (by omega)]
  unfold kiKeep
  rw [he]; rfl

/-- **Two keys' kept revisions differ** (a revision is one event's, of one key). -/
theorem IdxCRep.avail_inj {cmax : Int} {log : Log} (hb : LogB log) {idx : IndexM}
    (h : IdxCRep cmax (evsOf log) idx) {k1 k2 : GoString} {ki1 ki2 : KeyIndex} {c : w64} {r : Rev}
    (h1 : idxGet idx k1 = some ki1) (h2 : idxGet idx k2 = some ki2)
    (hr1 : kiAvail c ki1 = some r) (hr2 : kiAvail c ki2 = some r) : k1 = k2 := by
  obtain ⟨c1, -, -, rfl, -⟩ := h.get_some h1
  obtain ⟨c2, -, -, rfl, -⟩ := h.get_some h2
  obtain ⟨e1, he1, hr1', hk1⟩ := kiRevs_kiOfKey (kiRevs_kiCompact (kiAvail_mem hr1))
  obtain ⟨e2, he2, hr2', hk2⟩ := kiRevs_kiOfKey (kiRevs_kiCompact (kiAvail_mem hr2))
  have := evsOf_rev_inj log hb he1 he2 (hr1'.trans hr2'.symm)
  subst this
  rw [← hk1, ← hk2]

/-- **A compaction step** (`treeIndex.Compact`'s, under the lock): the key at `i` compacted at
`c' ≥ cmax`, deleted if that empties it; every key's level is then at most `c'`. -/
theorem IdxCRep.compactAt {cmax c' : Int} {log : Log} (hb : LogB log) {idx : IndexM}
    (h : IdxCRep cmax (evsOf log) idx) (hle : cmax ≤ c') (hc' : c' < 2 ^ 63)
    (i : Nat) (k : GoString) (ki : KeyIndex) (hi : idx[i]? = some (k, ki)) :
    IdxCRep c' (evsOf log)
      (if kiIsEmpty (kiCompact (W64 c') ki) then idx.eraseIdx i else idx.set i (k, kiCompact (W64 c') ki)) := by
  have hs := h.1
  have hmem : (k, ki) ∈ idx := List.mem_of_getElem? hi
  have hk : idxGet idx k = some ki := idxGet_of_mem idx hs _ hmem
  obtain ⟨c0, h0, h1, hki, -⟩ := h.get_some hk
  have hcc : kiCompact (W64 c') ki = kiCompact (W64 c') (kiOfKey (evsOf log) k) := by
    rw [hki]; exact kiCompact_kiCompact log hb k c0 c' h0 (by omega) hc'
  -- the other keys
  have hother : ∀ (idx' : IndexM), idx'.Pairwise idxLess →
      (∀ k', k' ≠ k → ∀ v, (k', v) ∈ idx' ↔ (k', v) ∈ idx) →
      ∀ k', k' ≠ k → ∃ c : Int, -1 ≤ c ∧ c ≤ c' ∧ idxGet idx' k' = kiCompactO c (kiOfKey (evsOf log) k') := by
    intro idx' hs' hm k' hk'
    obtain ⟨c1, h10, h11, h12⟩ := h.2 k'
    exact ⟨c1, h10, by omega, by rw [idxGet_congr hs hs' (hm k' hk'), h12]⟩
  split
  · rename_i he
    have hs' : (idx.eraseIdx i).Pairwise idxLess := hs.sublist (List.eraseIdx_sublist _ _)
    have hm : ∀ k', k' ≠ k → ∀ v, (k', v) ∈ idx.eraseIdx i ↔ (k', v) ∈ idx := by
      intro k' hk' v
      rw [List.mem_eraseIdx_iff_getElem?]
      constructor
      · rintro ⟨j, -, hj⟩; exact List.mem_of_getElem? hj
      · intro hv
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hv
        refine ⟨j, ?_, hj⟩
        rintro rfl
        rw [hi] at hj; cases hj; exact hk' rfl
    refine ⟨hs', fun k' => ?_⟩
    by_cases hk' : k' = k
    · subst hk'
      refine ⟨c', by omega, Int.le_refl _, ?_⟩
      unfold kiCompactO
      rw [← hcc, ite_eq_left he]
      apply idxGet_none_of_not_mem hs'
      intro v hv
      rw [List.mem_eraseIdx_iff_getElem?] at hv
      obtain ⟨j, hji, hj⟩ := hv
      exact hji (idx_key_unique hs hj hi rfl)
    · exact hother _ hs' hm k' hk'
  · rename_i he
    have hlt : i < idx.length := (List.getElem?_eq_some_iff.1 hi).1
    have hfst : (idx.set i (k, kiCompact (W64 c') ki)).map Prod.fst = idx.map Prod.fst := by
      rw [List.map_set]
      have : (idx.map Prod.fst)[i]'(by simp; exact hlt) = k := by
        simp only [List.getElem_map]
        rw [(List.getElem?_eq_some_iff.1 hi).2]
      simp only []
      rw [← this, List.set_getElem_self]
    have hs' : (idx.set i (k, kiCompact (W64 c') ki)).Pairwise idxLess := by
      have h2 : (idx.map Prod.fst).Pairwise go.GoStringLt := by
        rw [List.pairwise_map]; exact hs
      rw [← hfst, List.pairwise_map] at h2
      exact h2
    have hm : ∀ k', k' ≠ k → ∀ v, (k', v) ∈ idx.set i (k, kiCompact (W64 c') ki) ↔ (k', v) ∈ idx := by
      intro k' hk' v
      constructor
      · intro hv
        rcases List.mem_or_eq_of_mem_set hv with hv | hv
        · exact hv
        · cases hv; exact absurd rfl hk'
      · intro hv
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hv
        apply List.mem_of_getElem? (i := j)
        rw [List.getElem?_set]
        have hij : i ≠ j := by rintro rfl; rw [hi] at hj; cases hj; exact hk' rfl
        simp only [hij, ↓reduceIte]
        exact hj
    refine ⟨hs', fun k' => ?_⟩
    by_cases hk' : k' = k
    · subst hk'
      refine ⟨c', by omega, Int.le_refl _, ?_⟩
      unfold kiCompactO
      rw [← hcc, ite_eq_right he]
      apply idxGet_of_mem _ hs' (k', kiCompact (W64 c') ki)
      apply List.mem_of_getElem? (i := i)
      rw [List.getElem?_set_self hlt]
    · exact hother _ hs' hm k' hk'

end mvcc
end EtcdGrove
end Perennial
