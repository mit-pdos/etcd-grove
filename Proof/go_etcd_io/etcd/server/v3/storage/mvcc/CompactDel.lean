/-
The revisions index-driven compaction deletes (etcd-io/etcd#21951, `keyIndex.compact`'s `del`
map; `notes/pr-verify/etcd-21951.md`): the model `kiDel` of what `keyIndex.compact` adds to
`del`, and its facts.

* **Exactly what compaction drops from the index** (`kiRevs_kiDel`): a key index's revisions are
  `kiDel`'s followed by those of the compacted key index, in order. So the deleted revisions are
  every revision the index stops holding, each once, and nothing it keeps.
* **Below the compaction revision, never kept** (`kiDel_main_le`, `kiDel_lt_avail`): every deleted
  revision has a main at or below `c` and is below the revision compaction keeps for the key.
* **With the right tombstone mark** (`kiDel_tomb`): a deleted revision is marked a tombstone
  exactly when its event is a delete, so its bucket key is the one the backend holds.
* **For the index the tree holds** (`kiDel_ok`): every key's index there is a compacted index of
  a longer log (`IdxCRep`); what `kiDel` deletes of it at `rev` is a revision of the log certified
  at `rev`, with a main at or below `rev`, that compaction at `rev` does not keep (`DelOk`): a
  key compaction may delete (`KeyDel`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CompactIdx

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-! ### The model -/

/-- A generation's revisions as bucket keys, the last one marked a tombstone (`keyIndex.compact`'s
loop over a generation before `doCompact`'s: `j == len(revs)-1`). -/
def genDel (g : Gen) : List (Rev × Bool) :=
  g.revs.zipIdx.map fun p => (p.1, decide (p.2 + 1 = g.revs.length))

/-- What compaction cuts from the front of `doCompact`'s generation: the revisions before its
revision index (none if the generation is empty or has no revision at or below `c`). -/
def genCutDel (c : w64) (g : Gen) : List Rev :=
  if g.revs ≠ [] ∧ genWalk g.revs (pAbove c) ≠ -1 then
    g.revs.take (genWalk g.revs (pAbove c)).toNat else []

/-- **What `keyIndex.compact(atRev)` adds to `del`**: every revision of the generations before
`doCompact`'s (the last of each marked a tombstone), then the revisions of `doCompact`'s generation
before its revision index (not tombstones). -/
def kiDel (atRev : w64) (ki : KeyIndex) : List (Rev × Bool) :=
  ((ki.gens.take (compactGenIdx atRev ki.gens)).map genDel).flatten ++
    (genCutDel atRev (ki.gens.getD (compactGenIdx atRev ki.gens) Gen.empty)).map (fun r => (r, false))

/-! ### The revisions compaction drops -/

theorem genDel_fst (g : Gen) : (genDel g).map Prod.fst = g.revs := by
  unfold genDel
  rw [List.map_map]
  show (g.revs.zipIdx.map Prod.fst) = g.revs
  exact List.zipIdx_map_fst 0 _

theorem drop_set_cons {α : Type} {G : List α} {i : Nat} {x : α} (h : i < G.length) :
    (G.set i x).drop i = x :: G.drop (i + 1) := by
  apply List.ext_getElem?
  intro t
  rw [List.getElem?_drop, List.getElem?_set]
  cases t with
  | zero => simp [h]
  | succ t => simp only [List.getElem?_cons_succ, List.getElem?_drop]; rw [ite_eq_right (by omega)]; congr 1; omega

theorem genCutDel_split (c : w64) (g : Gen) : g.revs = genCutDel c g ++ (cutGen c g).revs := by
  unfold genCutDel cutGen
  split
  · simp only [List.take_append_drop]
  · simp

/-- A bucket key of `genDel`: a revision of the generation, marked when it is the last. -/
theorem mem_genDel {g : Gen} {r : Rev} {t : Bool} (h : (r, t) ∈ genDel g) :
    ∃ (p : Nat) (hp : p < g.revs.length), g.revs[p] = r ∧ t = decide (p + 1 = g.revs.length) := by
  unfold genDel at h
  rw [List.mem_map] at h
  obtain ⟨⟨r', p⟩, hm, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  rw [List.mem_zipIdx_iff_getElem?] at hm
  simp only at hm
  obtain ⟨hp, hpe⟩ := List.getElem?_eq_some_iff.1 hm
  exact ⟨p, hp, hpe, rfl⟩

/-- A revision of `genCutDel`: before the revision index, which is at or below `c`. -/
theorem mem_genCutDel {c : w64} {g : Gen} {r : Rev} (h : r ∈ genCutDel c g) :
    ∃ (ri p : Nat) (hri : ri < g.revs.length) (hp : p < ri), genWalk g.revs (pAbove c) = ri ∧
      g.revs[p] = r ∧ sint.Z g.revs[ri].main ≤ sint.Z c := by
  unfold genCutDel at h
  split at h
  · rename_i hc
    rcases genWalk_pAbove_spec g.revs c with ⟨h1, -⟩ | ⟨j, hj, h1, h2, -⟩
    · exact absurd h1 hc.2
    · rw [h1] at h
      simp only [Int.toNat_natCast] at h
      obtain ⟨p, hp, hpe⟩ := List.mem_iff_getElem.1 h
      rw [List.length_take] at hp
      refine ⟨j, p, hj, by omega, h1, ?_, h2⟩
      rw [← hpe, List.getElem_take]
  · simp at h

/-- A bucket key of `kiDel`: of a generation before `doCompact`'s, or cut from `doCompact`'s. -/
theorem mem_kiDel {c : w64} {ki : KeyIndex} {r : Rev} {t : Bool} (h : (r, t) ∈ kiDel c ki) :
    (∃ (j : Nat) (hj : j < ki.gens.length), j < compactGenIdx c ki.gens ∧ (r, t) ∈ genDel ki.gens[j]) ∨
      (r ∈ genCutDel c (ki.gens.getD (compactGenIdx c ki.gens) Gen.empty) ∧ t = false) := by
  unfold kiDel at h
  rcases List.mem_append.1 h with h | h
  · left
    rw [List.mem_flatten] at h
    obtain ⟨l, hl, hm⟩ := h
    rw [List.mem_map] at hl
    obtain ⟨g, hg, rfl⟩ := hl
    obtain ⟨j, hj, hje⟩ := List.mem_iff_getElem.1 hg
    rw [List.length_take] at hj
    refine ⟨j, by omega, by omega, ?_⟩
    rw [← hje, List.getElem_take] at hm
    exact hm
  · right
    rw [List.mem_map] at h
    obtain ⟨r', hr', he⟩ := h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨hr', rfl⟩

/-- Sorted revisions: each is at or below the last, main-wise. -/
theorem main_le_last {l : List Rev} (hs : l.Pairwise Rev.lt) {r : Rev} (hr : r ∈ l) :
    sint.Z r.main ≤ sint.Z (l.getLastD Rev.zero).main := by
  obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.1 hr
  have hne : l ≠ [] := by intro e; subst e; simp at hp
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  exact sorted_main_le hs (by omega) _

/-- A sorted key index's generations are sorted. -/
theorem gen_sorted_of {ki : KeyIndex} (hs : (kiRevs ki).Pairwise Rev.lt) {g : Gen} (hg : g ∈ ki.gens) :
    g.revs.Pairwise Rev.lt :=
  (List.pairwise_flatten.1 hs).1 _ (List.mem_map_of_mem hg)

/-- **The revisions compaction drops are `kiDel`'s**: a key index's revisions are those of
`kiDel` followed by those of the compacted key index. -/
theorem kiRevs_kiDel (c : w64) (ki : KeyIndex) :
    kiRevs ki = (kiDel c ki).map Prod.fst ++ kiRevs (kiCompact c ki) := by
  unfold kiRevs
  rw [kiCompact_gens]
  unfold kiDel
  generalize ki.gens = G
  rcases Classical.em (G = []) with rfl | hne
  · simp [compactGenIdx, genCutDel, Gen.empty]
  have hlt := compactGenIdx_lt c G hne
  generalize compactGenIdx c G = gi at *
  rw [drop_set_cons hlt, getD_lt _ hlt]
  rw [List.map_append, List.map_flatten, List.map_map, List.map_map]
  have hfd : (Prod.fst ∘ fun r => (r, false)) = (id : Rev → Rev) := rfl
  rw [hfd, List.map_id]
  have hgd : (List.map Prod.fst ∘ genDel) = Gen.revs := by funext g; exact genDel_fst g
  rw [hgd]
  conv => lhs; rw [← List.take_append_drop gi G, List.drop_eq_getElem_cons hlt]
  rw [List.map_append, List.flatten_append, List.map_cons, List.map_cons, List.flatten_cons,
    List.flatten_cons, genCutDel_split c G[gi]]
  simp only [List.append_assoc]

/-- The revision compaction keeps is one the compacted key index has. -/
theorem kiAvail_mem_kiCompact {c : w64} {ki : KeyIndex} {r : Rev} (h : kiAvail c ki = some r) :
    r ∈ kiRevs (kiCompact c ki) := by
  unfold kiAvail at h
  simp only [] at h
  split at h
  · cases h
  rename_i hw
  simp only [Option.some.injEq] at h
  subst h
  unfold kiRevs
  rw [kiCompact_gens]
  generalize hG : ki.gens = G at *
  rcases Classical.em (G = []) with rfl | hne
  · simp [compactGenIdx, Gen.empty, genWalk] at hw
  have hlt := compactGenIdx_lt c G hne
  generalize compactGenIdx c G = gi at *
  rw [drop_set_cons hlt]
  generalize hg : G.getD gi Gen.empty = g at *
  have hr := genWalk_range g.revs (pAbove c)
  have hlt' : (genWalk g.revs (pAbove c)).toNat < g.revs.length := by omega
  have hne' : g.revs ≠ [] := by intro e; rw [e] at hlt'; simp at hlt'
  rw [List.mem_flatten]
  refine ⟨(cutGen c g).revs, List.mem_map_of_mem List.mem_cons_self, ?_⟩
  unfold cutGen
  rw [ite_eq_left ⟨hne', hw⟩, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt']
  simp only [Option.getD_some]
  rw [List.drop_eq_getElem_cons hlt']
  exact List.mem_cons_self

/-- Every revision `kiDel` deletes is below the one compaction keeps (of a sorted key index). -/
theorem kiDel_lt_avail {c : w64} {ki : KeyIndex} (hs : (kiRevs ki).Pairwise Rev.lt) {r a : Rev}
    {t : Bool} (hr : (r, t) ∈ kiDel c ki) (ha : kiAvail c ki = some a) : Rev.lt r a := by
  have hsplit := kiRevs_kiDel c ki
  rw [hsplit, List.pairwise_append] at hs
  exact hs.2.2 r (List.mem_map.2 ⟨(r, t), hr, rfl⟩) a (kiAvail_mem_kiCompact ha)

/-- Every revision `kiDel` deletes has a main at or below `c` (of a sorted key index). -/
theorem kiDel_main_le {c : w64} {ki : KeyIndex} (hs : (kiRevs ki).Pairwise Rev.lt) {r : Rev}
    {t : Bool} (hr : (r, t) ∈ kiDel c ki) : sint.Z r.main ≤ sint.Z c := by
  rcases mem_kiDel hr with ⟨j, hj, hjg, hm⟩ | ⟨hm, -⟩
  · obtain ⟨p, hp, rfl, -⟩ := mem_genDel hm
    have hb := compactGenIdx_before c ki.gens j hjg
    rw [getD_lt _ hj] at hb
    unfold tombZ at hb
    have := main_le_last (gen_sorted_of hs (List.getElem_mem hj)) (List.getElem_mem hp)
    omega
  · obtain ⟨ri, p, hri, hpr, -, rfl, hle⟩ := mem_genCutDel hm
    have hgs : (ki.gens.getD (compactGenIdx c ki.gens) Gen.empty).revs.Pairwise Rev.lt := by
      rcases Classical.em (compactGenIdx c ki.gens < ki.gens.length) with hl | hl
      · rw [getD_lt _ hl]; exact gen_sorted_of hs (List.getElem_mem hl)
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; simp [Gen.empty]
    have := sorted_main_le hgs (Nat.le_of_lt hpr) hri
    omega

/-- **The tombstone mark is the event's**: of a key index whose revisions are events of `evs` of
key `k` (`KiEvs`: a tombstone exactly when it ends a generation that is not the last), each
revision `kiDel` deletes is an event of `k` that is a delete exactly when it is marked one. -/
theorem kiDel_tomb {evs : List Ev} {k : GoString} {ki : KeyIndex} (h : KiEvs evs k ki)
    (hne : ki.gens ≠ []) (c : w64) {r : Rev} {t : Bool} (hr : (r, t) ∈ kiDel c ki) :
    ∃ e ∈ evs, e.rev = r ∧ e.key = k ∧ e.tomb = t := by
  have hlt := compactGenIdx_lt c ki.gens hne
  rcases mem_kiDel hr with ⟨j, hj, hjg, hm⟩ | ⟨hm, rfl⟩
  · obtain ⟨p, hp, hpr, rfl⟩ := mem_genDel hm
    obtain ⟨e, he, h1, h2, h3⟩ := h j p ki.gens[j] r (List.getElem?_eq_getElem hj)
      (by rw [List.getElem?_eq_getElem hp, hpr])
    refine ⟨e, he, h1, h2, ?_⟩
    have h3' : e.tomb = true ↔ p + 1 = ki.gens[j].revs.length := by
      rw [h3]; constructor
      · exact fun x => x.2
      · exact fun x => ⟨by omega, x⟩
    cases ht : e.tomb
    · rw [ht] at h3'; simp only [Bool.false_eq_true, false_iff] at h3'; simp [h3']
    · rw [ht] at h3'; simp only [true_iff] at h3'; simp [h3']
  · rw [getD_lt _ hlt] at hm
    obtain ⟨ri, p, hri, hpr, -, hpe, -⟩ := mem_genCutDel hm
    obtain ⟨e, he, h1, h2, h3⟩ := h _ p _ r (List.getElem?_eq_getElem hlt)
      (by rw [List.getElem?_eq_getElem (by omega), hpe])
    refine ⟨e, he, h1, h2, ?_⟩
    cases ht : e.tomb
    · rfl
    · rw [ht] at h3; have := (h3.1 rfl).2; omega

/-- Compaction keeps `KiEvs`: the compacted generations are the old ones from `doCompact`'s on,
that one cut at the front (its last revision stays its last). -/
theorem KiEvs.kiCompact {evs : List Ev} {k : GoString} {ki : KeyIndex} (h : KiEvs evs k ki)
    (c : w64) : KiEvs evs k (mvcc.kiCompact c ki) := by
  intro i p g r hg hr
  have hG := kiCompact_gens c ki
  rw [hG] at hg
  have hlen : (mvcc.kiCompact c ki).gens.length = ki.gens.length - compactGenIdx c ki.gens := by
    rw [hG, dropSet_length]
  rw [hlen]
  rcases Classical.em (ki.gens = []) with he | hne
  · rw [he] at hg; simp at hg
  have hlt := compactGenIdx_lt c ki.gens hne
  generalize hgi : compactGenIdx c ki.gens = gi at *
  rw [drop_set_cons hlt, getD_lt _ hlt] at hg
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hg
    subst hg
    rcases cutGen_cases c ki.gens[gi] with hc | ⟨j, hj, -, -, hc, -⟩
    · rw [hc] at hr ⊢
      obtain ⟨e, he, h1, h2, h3⟩ := h gi p _ r (List.getElem?_eq_getElem hlt) hr
      refine ⟨e, he, h1, h2, ?_⟩
      rw [h3]; constructor
      · rintro ⟨a, b⟩; exact ⟨by omega, b⟩
      · rintro ⟨a, b⟩; exact ⟨by omega, b⟩
    · rw [hc] at hr ⊢
      rw [List.getElem?_drop] at hr
      obtain ⟨e, he, h1, h2, h3⟩ := h gi (j + p) _ r (List.getElem?_eq_getElem hlt) hr
      refine ⟨e, he, h1, h2, ?_⟩
      rw [h3, List.length_drop]; constructor
      · rintro ⟨a, b⟩; exact ⟨by omega, by omega⟩
      · rintro ⟨a, b⟩
        have : p < ki.gens[gi].revs.length - j := by
          have := (List.getElem?_eq_some_iff.1 hr).1; omega
        exact ⟨by omega, by omega⟩
  | succ i =>
    simp only [List.getElem?_cons_succ, List.getElem?_drop] at hg
    obtain ⟨e, he, h1, h2, h3⟩ := h (gi + 1 + i) p g r hg hr
    refine ⟨e, he, h1, h2, ?_⟩
    rw [h3]; constructor
    · rintro ⟨a, b⟩; exact ⟨by omega, b⟩
    · rintro ⟨a, b⟩; exact ⟨by omega, b⟩

/-! ### For the index the tree holds -/

/-- **A revision compaction at `c` may delete, with its mark** (of the log certified at `c`): its
main is in `[0, c]`, compaction at `c` keeps no key's revision `r`, and `r` is an event of the log
that is a delete exactly when `t`. -/
def DelOk (log : Log) (c : Int) (r : Rev) (t : Bool) : Prop :=
  0 ≤ sint.Z r.main ∧ sint.Z r.main ≤ c ∧ ¬ keepAt log c r ∧
    ∃ e ∈ evsOf log, e.rev = r ∧ e.tomb = t

/-- A revision compaction may delete is, as a bucket key, a key compaction may delete. -/
theorem DelOk.keyDel {log : Log} {c : Int} {r : Rev} {t : Bool} (h : DelOk log c r t)
    (hc : c < log.length) : KeyDel log c (revBytes r t) :=
  ⟨hc, r, t, rfl, h.1, h.2.1, h.2.2.1⟩

/-- **What `keyIndex.compact` deletes of a key the tree holds** (`treeIndex.Compact`'s step): the
key's index is a compacted index (at a level `cz`) of the current log `ilog ++ [pend]`, which
extends the log `log₀` certified at `rev`; each revision `kiDel` deletes of it at `rev` is one
compaction at `rev` may delete, with its mark (`DelOk`). -/
theorem kiDel_ok (log₀ ilog : Log) (pend : List Change)
    (hcmp : histOf log₀ <+: histShape ilog pend ∨ histShape ilog pend <+: histOf log₀)
    (hcount : (evsOf log₀).length ≤ (evsOf (ilog ++ [pend])).length)
    (hb : LogB (ilog ++ [pend])) (hb0 : LogB log₀)
    (k : GoString) (cz : Int) (hcz : -1 ≤ cz) (rev : w64) (hcr : cz ≤ sint.Z rev)
    (hrl : sint.Z rev < log₀.length) {r : Rev} {t : Bool}
    (hr : (r, t) ∈ kiDel rev (mvcc.kiCompact (W64 cz) (kiOfKey (evsOf (ilog ++ [pend])) k))) :
    DelOk log₀ (sint.Z rev) r t := by
  generalize hX : kiOfKey (evsOf (ilog ++ [pend])) k = X at hr
  have hS : KiS X := hX ▸ kiOfKey_KiS (ilog ++ [pend]) hb k
  generalize hZ : mvcc.kiCompact (W64 cz) X = Z at hr
  have hsplit := kiRevs_kiDel (W64 cz) X
  rw [hZ] at hsplit
  have hsZ : (kiRevs Z).Pairwise Rev.lt := by
    have := hS.sorted; rw [hsplit, List.pairwise_append] at this; exact this.2.1
  have hrZ : r ∈ kiRevs Z := by
    rw [kiRevs_kiDel rev Z]; exact List.mem_append_left _ (List.mem_map.2 ⟨(r, t), hr, rfl⟩)
  have hrX : r ∈ kiRevs X := by rw [← hZ] at hrZ; exact kiRevs_kiCompact hrZ
  have hne : Z.gens ≠ [] := by rw [← hZ]; exact (kiCompact_gensOk hS.wf _).1
  have hev : KiEvs (evsOf (ilog ++ [pend])) k Z := by
    rw [← hZ]; exact (hX ▸ (kiOfKey_struct k (evsOf (ilog ++ [pend]))).2.2).kiCompact _
  obtain ⟨e, he, h1, h2, h3⟩ := kiDel_tomb hev hne rev hr
  have hmain := kiDel_main_le hsZ hr
  have hlen : ilog.length < 2 ^ 63 := by have := hb.1; simp at this; omega
  obtain ⟨rest, hrest, hfrom⟩ := reader_prefix_from log₀ ilog pend hcmp hcount hlen
  have he0 : e ∈ evsOf log₀ := by
    rw [hrest] at he
    rcases List.mem_append.1 he with h | h
    · exact h
    · have := hfrom e h; rw [h1] at this; omega
  refine ⟨hS.nonneg r hrX, hmain, ?_, e, he0, h1, h3⟩
  rintro ⟨k', hk'⟩
  obtain ⟨e', he', h1', h2'⟩ := kiRevs_kiOfKey (kiAvail_mem hk')
  have hee := evsOf_rev_inj log₀ hb0 he0 he' (h1.trans h1'.symm)
  subst hee
  have hkk : k' = k := h2'.symm.trans h2
  subst hkk
  have hW : W64 (sint.Z rev) = rev := by word
  have hav : kiAvail rev Z = some r := by
    have hrz : sint.Z rev < 2 ^ 63 := by word
    rw [← hZ, ← hX, ← hW, kiAvail_kiCompact (ilog ++ [pend]) hb k' cz (sint.Z rev) hcz hcr hrz,
      reader_avail log₀ ilog pend hcmp hcount hlen hb0 k' (sint.Z rev) (by word) hrl]
    exact hk'
  exact Rev.lt_irrefl r (kiDel_lt_avail hsZ hr hav)

end mvcc
end EtcdGrove
end Perennial
