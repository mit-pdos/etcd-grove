/-
**The index at a full revision** (`notes/m2-storage-plan.md`, "The index at a full revision (branch
m2-index)"; the user's decision B1 after review round 5): a key index cut at a full revision (a main
and a sub-revision), the pure facts about it, and the index invariant over such cuts (`IdxCRepN`), up
to the unread header of a tombstone-only generation (`kiNorm`). Lean-first, pure.

**Why a full revision.** `restore()` rebuilds the index from the `Key` bucket, which a compaction job
may have thinned in batches (`scheduleCompaction`): a batch can stop between two sub-revisions of
one main revision, and one main revision can change a key twice (a put and a delete in sibling
transactions, `issues/etcd-txn-check-intervals-sibling.md`). The rebuilt key index then starts at
the key's first surviving revision, which no compaction at a *main* revision gives
(`M2StorageDraftIndex.lean`'s `cx3_not_compacted`). So the invariant's per-key level is a revision
of the key: the key index is the log's with every revision before that one dropped (`kiCutAt`, the
position of the revision in the key index: its generation `gi` and its index `j` there), at or
before what compaction at some `c ≤ cmax` keeps (`CutLe`). A compaction at `c` is such a cut
(`kiCompact_eq_cutAt`); a compaction at `c' ≥ c` erases the difference (`kiCompact_cutAt`); a reader
at or above `c` cannot tell (`kiGet_cutAt`); and neither can `doCompact`'s and `keep`'s choices
(`kiAvail_cutAt`, `kiKeep_cutAt`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.CompactIdx

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-! ## The cut -/

/-- A generation without its first `j` revisions (the header kept). -/
def genDrop (j : Nat) (g : Gen) : Gen := { g with revs := g.revs.drop j }

/-- **A key index cut at a full revision**, the revision at position `j` of generation `gi`: the
generations before `gi` dropped, generation `gi` cut to start at that revision (its header kept),
the later ones and `modified` unchanged. `kiCompact` is the cut at the position `doCompact` picks
(`kiCompact_eq_cutAt`). -/
def kiCutAt (gi j : Nat) (ki : KeyIndex) : KeyIndex :=
  { ki with gens := (ki.gens.set gi (genDrop j (ki.gens.getD gi Gen.empty))).drop gi }

/-- The cut, or nothing if it is empty (`treeIndex` has no such key). -/
def kiCutO (gi j : Nat) (ki : KeyIndex) : Option KeyIndex :=
  if kiIsEmpty (kiCutAt gi j ki) then none else some (kiCutAt gi j ki)

/-- The revision index `doCompact` cuts its generation at (`0` if the walk finds none). -/
def cmpRevIdx (c : w64) (ki : KeyIndex) : Nat :=
  (genWalk (ki.gens.getD (compactGenIdx c ki.gens) Gen.empty).revs (pAbove c)).toNat

/-- **The position `(gi, j)` is at or before the one compaction at `c` cuts at**: a revision of an
earlier generation, or of `doCompact`'s generation at or before its revision. -/
def CutLe (c : w64) (ki : KeyIndex) (gi j : Nat) : Prop :=
  (gi < compactGenIdx c ki.gens ∧ j < (ki.gens.getD gi Gen.empty).revs.length) ∨
    (gi = compactGenIdx c ki.gens ∧ j ≤ cmpRevIdx c ki)

theorem genDrop_zero (g : Gen) : genDrop 0 g = g := by
  cases g; simp [genDrop]

theorem genDrop_revs (j : Nat) (g : Gen) : (genDrop j g).revs = g.revs.drop j := rfl

theorem kiCutAt_gens (gi j : Nat) (ki : KeyIndex) :
    (kiCutAt gi j ki).gens = (ki.gens.set gi (genDrop j (ki.gens.getD gi Gen.empty))).drop gi := rfl

theorem kiCutAt_modified (gi j : Nat) (ki : KeyIndex) : (kiCutAt gi j ki).modified = ki.modified :=
  rfl

theorem cutGen_eq_genDrop (c : w64) (g : Gen) :
    cutGen c g = genDrop (genWalk g.revs (pAbove c)).toNat g := by
  unfold cutGen
  split
  · rfl
  · rename_i h
    by_cases he : g.revs = []
    · cases g; simp only at he; subst he; simp [genDrop]
    · have hw : genWalk g.revs (pAbove c) = -1 := by
        by_cases hw : genWalk g.revs (pAbove c) = -1
        · exact hw
        · exact absurd ⟨he, hw⟩ h
      rw [hw]; exact (genDrop_zero g).symm

/-- **A compaction is a cut** (at the position `doCompact` picks). -/
theorem kiCompact_eq_cutAt (c : w64) (ki : KeyIndex) :
    kiCompact c ki = kiCutAt (compactGenIdx c ki.gens) (cmpRevIdx c ki) ki := by
  refine KeyIndex.ext' rfl ?_
  rw [kiCompact_gens, kiCutAt_gens, cutGen_eq_genDrop]
  rfl

theorem kiCompactO_eq_cutO (c : Int) (ki : KeyIndex) :
    kiCompactO c ki = kiCutO (compactGenIdx (W64 c) ki.gens) (cmpRevIdx (W64 c) ki) ki := by
  unfold kiCompactO kiCutO
  rw [kiCompact_eq_cutAt]

theorem CutLe.cmp (c : w64) (ki : KeyIndex) : CutLe c ki (compactGenIdx c ki.gens) (cmpRevIdx c ki) :=
  Or.inr ⟨rfl, Nat.le_refl _⟩

theorem cmpRevIdx_lt (c : w64) (ki : KeyIndex)
    (hne : (ki.gens.getD (compactGenIdx c ki.gens) Gen.empty).revs ≠ []) :
    cmpRevIdx c ki < (ki.gens.getD (compactGenIdx c ki.gens) Gen.empty).revs.length := by
  unfold cmpRevIdx
  have := genWalk_range (ki.gens.getD (compactGenIdx c ki.gens) Gen.empty).revs (pAbove c)
  have : 0 < (ki.gens.getD (compactGenIdx c ki.gens) Gen.empty).revs.length :=
    List.length_pos_iff.2 hne
  omega

/-- The cut's position: generation `gi` is one, and the revision index is in it (or the
generation is empty and the index `0`). -/
theorem CutLe.pos {c : w64} {ki : KeyIndex} (hwf : KiWf ki) {gi j : Nat} (h : CutLe c ki gi j) :
    gi ≤ compactGenIdx c ki.gens ∧ gi < ki.gens.length ∧
      (j < (ki.gens.getD gi Gen.empty).revs.length ∨ ((ki.gens.getD gi Gen.empty).revs = [] ∧ j = 0)) := by
  have hlt := compactGenIdx_lt c ki.gens hwf.ne
  rcases h with ⟨h1, h2⟩ | ⟨rfl, h2⟩
  · exact ⟨Nat.le_of_lt h1, by omega, Or.inl h2⟩
  · refine ⟨Nat.le_refl _, hlt, ?_⟩
    by_cases he : (ki.gens.getD (compactGenIdx c ki.gens) Gen.empty).revs = []
    · right; refine ⟨he, ?_⟩
      have : cmpRevIdx c ki = 0 := by
        unfold cmpRevIdx; rw [he, genWalk_eq_none (by simp)]; rfl
      omega
    · left; have := cmpRevIdx_lt c ki he; omega

theorem tombZ_genDrop {j : Nat} {g : Gen} (h : j < g.revs.length ∨ (g.revs = [] ∧ j = 0)) :
    tombZ (genDrop j g) = tombZ g := by
  unfold tombZ
  rw [genDrop_revs]
  rcases h with h | ⟨he, rfl⟩
  · rw [List.getLastD_eq_getLast?, List.getLastD_eq_getLast?, List.getLast?_drop,
      ite_eq_right (by omega)]
  · rw [List.drop_zero]

theorem genDrop_revs_ne {j : Nat} {g : Gen} (h : j < g.revs.length ∨ (g.revs = [] ∧ j = 0)) :
    (genDrop j g).revs = [] ↔ g.revs = [] := by
  rw [genDrop_revs]
  rcases h with h | ⟨he, rfl⟩
  · constructor
    · intro h'; have := congrArg List.length h'; simp at this; omega
    · intro h'; rw [h'] at h; simp at h
  · simp

/-- The walk at `c ≤ c'` in `doCompact`'s generation stops at or after the cut. -/
theorem cmpRevIdx_le_walk {c c' : w64} (hcc : sint.Z c ≤ sint.Z c') (g : Gen) {j : Nat}
    (hj : j ≤ (genWalk g.revs (pAbove c)).toNat) (hj0 : 0 < j) :
    (j : Int) ≤ genWalk g.revs (pAbove c') := by
  rcases genWalk_pAbove_spec g.revs c with ⟨h1, -⟩ | ⟨m, hm, h1, h2, -⟩
  · rw [h1] at hj; simp at hj; omega
  · rw [h1] at hj
    simp only [Int.toNat_natCast] at hj
    have := genWalk_ge (p := pAbove c') hm (by simp [pAbove]; omega)
    omega

/-! ## Compaction above the cut -/

/-- `doCompact`'s generation in the cut (at `c' ≥ c`): the original's, shifted. -/
theorem compactGenIdx_cutAt {c c' : w64} {ki : KeyIndex} (hwf : KiWf ki) (hcc : sint.Z c ≤ sint.Z c')
    {gi j : Nat} (h : CutLe c ki gi j) :
    gi ≤ compactGenIdx c' ki.gens ∧
    compactGenIdx c' (kiCutAt gi j ki).gens = compactGenIdx c' ki.gens - gi := by
  have hne := hwf.ne
  obtain ⟨hgc, hlt, hj⟩ := h.pos hwf
  have hge0 := (compactGenIdx_compact_ge hwf c c' hcc).1
  have hge : gi ≤ compactGenIdx c' ki.gens := by omega
  have hlt' := compactGenIdx_lt c' ki.gens hne
  refine ⟨hge, ?_⟩
  have htomb := tombZ_genDrop hj
  generalize hm : compactGenIdx c' ki.gens = m at *
  rw [kiCutAt_gens]
  apply compactGenIdx_eq
  · rw [dropSet_length]; omega
  · intro t ht
    cases t with
    | zero =>
      rw [dropSet_getD0 _ _ _ _ hlt, dropSet_getDs _ _ 0, genAdv_tomb _ htomb,
        show gi + 0 + 1 = gi + 1 by omega]
      exact compactGenIdx_before c' ki.gens gi (by rw [hm]; omega)
    | succ t =>
      rw [dropSet_getDs, dropSet_getDs, show gi + (t + 1) + 1 = gi + t + 1 + 1 by omega]
      exact compactGenIdx_before c' ki.gens (gi + t + 1) (by rw [hm]; omega)
  · rcases compactGenIdx_stop c' ki.gens hne with h' | h'
    · left; rw [dropSet_length]; omega
    · right
      rw [hm] at h'
      rcases Nat.lt_or_eq_of_le hge with hgt | heq
      · rw [show m - gi = (m - gi - 1) + 1 by omega, dropSet_getDs, dropSet_getDs,
          show gi + (m - gi - 1) + 1 = m by omega, show gi + (m - gi - 1 + 1) + 1 = m + 1 by omega]
        exact h'
      · subst heq
        rw [Nat.sub_self, dropSet_getD0 _ _ _ _ hlt, dropSet_getDs _ _ 0, genAdv_tomb _ htomb]
        exact h'

/-- If the cut is in `doCompact`'s generation at `c'`, it is at or before the walk's stop there. -/
theorem CutLe.walk {c c' : w64} {ki : KeyIndex} (hwf : KiWf ki) (hcc : sint.Z c ≤ sint.Z c')
    {gi j : Nat} (h : CutLe c ki gi j) (hgi : gi = compactGenIdx c' ki.gens) (hj0 : 0 < j) :
    (j : Int) ≤ genWalk (ki.gens.getD gi Gen.empty).revs (pAbove c') := by
  have hge0 := (compactGenIdx_compact_ge hwf c c' hcc).1
  rcases h with ⟨h1, -⟩ | ⟨rfl, h2⟩
  · omega
  · exact cmpRevIdx_le_walk hcc _ h2 hj0

theorem cutGen_genDrop {c : w64} {g : Gen} {j : Nat} (hj : (j : Int) ≤ genWalk g.revs (pAbove c)) :
    cutGen c (genDrop j g) = cutGen c g := by
  have hwlt := genWalk_lt g.revs (pAbove c)
  have hne : g.revs ≠ [] := by intro h; have := hj; rw [h, genWalk_nil] at this; omega
  have hne' : (genDrop j g).revs ≠ [] := by
    rw [genDrop_revs]; intro h; have := congrArg List.length h; simp at this; omega
  unfold cutGen
  rw [genDrop_revs] at hne' ⊢
  rw [genWalk_drop hj, ite_eq_left ⟨hne', by omega⟩, ite_eq_left ⟨hne, by omega⟩]
  unfold genDrop
  simp only [List.drop_drop]
  congr 2; omega

/-- **Compaction at `c' ≥ c` erases the cut.** -/
theorem kiCompact_cutAt {c c' : w64} {ki : KeyIndex} (hwf : KiWf ki) (hcc : sint.Z c ≤ sint.Z c')
    {gi j : Nat} (h : CutLe c ki gi j) : kiCompact c' (kiCutAt gi j ki) = kiCompact c' ki := by
  obtain ⟨hge, hidx⟩ := compactGenIdx_cutAt hwf hcc h
  obtain ⟨-, hlt, -⟩ := h.pos hwf
  refine KeyIndex.ext' rfl ?_
  rw [kiCompact_gens c' (kiCutAt gi j ki), hidx, kiCutAt_gens, kiCompact_gens c' ki]
  have hwalk := fun hgi hj0 => h.walk hwf hcc hgi hj0
  generalize compactGenIdx c' ki.gens = m at *
  rcases Nat.lt_or_eq_of_le hge with hgt | heq
  · rw [show m - gi = (m - gi - 1) + 1 by omega, dropSet_getDs,
      show gi + (m - gi - 1) + 1 = m by omega, show m - gi - 1 + 1 = m - gi by omega]
    exact dropSet_dropSet _ _ _ _ _ hgt
  · subst heq
    rw [Nat.sub_self, dropSet_getD0 _ _ _ _ hlt, List.drop_zero, dropSet_set0 _ _ _ _ hlt]
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; rw [genDrop_zero]
    · rw [cutGen_genDrop (hwalk rfl hj)]

/-- `doCompact`'s choice at `c' ≥ c` is the same on the cut. -/
theorem kiAvail_cutAt {c c' : w64} {ki : KeyIndex} (hwf : KiWf ki) (hcc : sint.Z c ≤ sint.Z c')
    {gi j : Nat} (h : CutLe c ki gi j) : kiAvail c' (kiCutAt gi j ki) = kiAvail c' ki := by
  obtain ⟨hge, hidx⟩ := compactGenIdx_cutAt hwf hcc h
  obtain ⟨-, hlt, -⟩ := h.pos hwf
  have hwalk := fun hgi hj0 => h.walk hwf hcc hgi hj0
  unfold kiAvail
  simp only []
  rw [hidx, kiCutAt_gens]
  generalize compactGenIdx c' ki.gens = m at *
  rcases Nat.lt_or_eq_of_le hge with hgt | heq
  · rw [show m - gi = (m - gi - 1) + 1 by omega, dropSet_getDs, show gi + (m - gi - 1) + 1 = m by omega]
  · subst heq
    rw [Nat.sub_self, dropSet_getD0 _ _ _ _ hlt]
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; rw [genDrop_zero]
    · have hw' := hwalk rfl hj
      generalize ki.gens.getD gi Gen.empty = g at *
      rw [genDrop_revs, genWalk_drop hw', ite_eq_right (by omega), ite_eq_right (by omega)]
      congr 1
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
      congr 2; omega

theorem keepOf_genDrop {c' : w64} {g : Gen} {j : Nat} (hj : (j : Int) ≤ genWalk g.revs (pAbove c'))
    (l : Prop) [Decidable l] : keepOf c' (genDrop j g) l = keepOf c' g l := by
  have hwr := genWalk_range g.revs (pAbove c')
  unfold keepOf
  simp only []
  rw [genDrop_revs, genWalk_drop hj]
  generalize hW : genWalk g.revs (pAbove c') = W at *
  have hne : g.revs.drop j ≠ [] := by
    intro h; have := congrArg List.length h; simp at this; omega
  have hne' : g.revs ≠ [] := by intro h; rw [h] at hwr; simp at hwr; omega
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

/-- `keep`'s choice at `c' ≥ c` is the same on the cut. -/
theorem kiKeep_cutAt {c c' : w64} {ki : KeyIndex} (hwf : KiWf ki) (hcc : sint.Z c ≤ sint.Z c')
    {gi j : Nat} (h : CutLe c ki gi j) : kiKeep c' (kiCutAt gi j ki) = kiKeep c' ki := by
  obtain ⟨hge, hidx⟩ := compactGenIdx_cutAt hwf hcc h
  obtain ⟨-, hlt, -⟩ := h.pos hwf
  have hlt' := compactGenIdx_lt c' ki.gens hwf.ne
  have hwalk := fun hgi hj0 => h.walk hwf hcc hgi hj0
  rw [kiKeep_keepOf, kiKeep_keepOf, hidx, kiCutAt_gens, dropSet_length]
  generalize compactGenIdx c' ki.gens = m at *
  rcases Nat.lt_or_eq_of_le hge with hgt | heq
  · rw [show m - gi = (m - gi - 1) + 1 by omega, dropSet_getDs, show gi + (m - gi - 1) + 1 = m by omega]
    apply keepOf_congr; omega
  · subst heq
    rw [Nat.sub_self, dropSet_getD0 _ _ _ _ hlt]
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj; rw [genDrop_zero]; apply keepOf_congr; omega
    · rw [keepOf_genDrop (hwalk rfl hj)]; apply keepOf_congr; omega

/-! ## Readers above the cut -/

/-- Below the cut's generation, the scan finds nothing (their tombstones are at or below `c`). -/
theorem findAux_below_cut {ki : KeyIndex} (hwf : KiWf ki) {c a : w64} (hca : sint.Z c ≤ sint.Z a)
    {gi : Nat} (hgi : gi ≤ compactGenIdx c ki.gens) : kiFindGenAux ki.gens a gi = none := by
  have hlt := compactGenIdx_lt c ki.gens hwf.ne
  cases gi with
  | zero => rfl
  | succ m =>
    have hb := compactGenIdx_before_le c ki.gens m (by omega)
    apply kiFindGenAux_tomb
    · exact hwf.nonlast m (by omega)
    · omega
    · unfold tombZ at hb; omega

/-- The cut's scan is the scan, shifted. -/
theorem findAux_cutAt {ki : KeyIndex} (hs : KiS ki) {c a : w64} (hca : sint.Z c ≤ sint.Z a)
    {gi j : Nat} (h : CutLe c ki gi j) :
    ∀ t, t < ki.gens.length - gi →
      kiFindGenAux (kiCutAt gi j ki).gens a (t + 1) =
        (kiFindGenAux ki.gens a (gi + t + 1)).map (fun x => x - gi) ∧
      ∀ x, kiFindGenAux ki.gens a (gi + t + 1) = some x → gi ≤ x := by
  have hwf := hs.wf
  obtain ⟨hgc, hlt, hj⟩ := h.pos hwf
  have hG : (kiCutAt gi j ki).gens = (ki.gens.set gi (genDrop j (ki.gens.getD gi Gen.empty))).drop gi :=
    kiCutAt_gens gi j ki
  have hlen : (kiCutAt gi j ki).gens.length = ki.gens.length - gi := by rw [hG, dropSet_length]
  have hnone := findAux_below_cut hwf hca hgc
  intro t
  induction t with
  | zero =>
    intro _
    rw [kiFindGenAux_succ, show gi + 0 + 1 = gi + 1 by omega, kiFindGenAux_succ]
    rw [show (kiCutAt gi j ki).gens.getD 0 Gen.empty = genDrop j (ki.gens.getD gi Gen.empty) by
      rw [hG, dropSet_getD0 _ _ _ _ hlt]]
    rw [hlen]
    have hjj := hj
    generalize hg : ki.gens.getD gi Gen.empty = g at hjj
    simp only []
    have hrne := genDrop_revs_ne hjj
    have htz := tombZ_genDrop hjj
    unfold tombZ at htz
    by_cases he : g.revs = []
    · have he' : (genDrop j g).revs = [] := hrne.2 he
      simp only [he, he', ↓reduceIte, hnone, Option.map_none, kiFindGenAux_zero]
      exact ⟨by trivial, fun x hx => by cases hx⟩
    · have he' : (genDrop j g).revs ≠ [] := fun h' => he (hrne.1 h')
      simp only [he, he', ↓reduceIte]
      rw [show sint.Z ((genDrop j g).revs.getLastD Rev.zero).main =
        sint.Z (g.revs.getLastD Rev.zero).main from htz]
      have hiff : (0 ≠ ki.gens.length - gi - 1) ↔ (gi ≠ ki.gens.length - 1) := by omega
      by_cases ht : gi ≠ ki.gens.length - 1 ∧ sint.Z (g.revs.getLastD Rev.zero).main ≤ sint.Z a
      · have ht' : 0 ≠ ki.gens.length - gi - 1 ∧ sint.Z (g.revs.getLastD Rev.zero).main ≤ sint.Z a :=
          ⟨hiff.2 ht.1, ht.2⟩
        simp only [ht, ht', ne_eq]
        exact ⟨by trivial, fun x hx => by cases hx⟩
      · have ht' : ¬ (0 ≠ ki.gens.length - gi - 1 ∧ sint.Z (g.revs.getLastD Rev.zero).main ≤ sint.Z a) := by
          rw [hiff]; exact ht
        rw [ite_eq_right ht, ite_eq_right ht']
        rcases Nat.eq_zero_or_pos j with hj0 | hj0
        · subst hj0
          rw [genDrop_zero]
          split
          · simp
          · simp [hnone, kiFindGenAux_zero]
        · -- the cut is in `doCompact`'s generation at `c`, at or before its walk's stop
          have hgi : gi = compactGenIdx c ki.gens := by
            rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
            · exfalso
              apply ht
              refine ⟨by have := compactGenIdx_lt c ki.gens hwf.ne; omega, ?_⟩
              have hb := compactGenIdx_before_le c ki.gens gi h1
              rw [hg] at hb
              unfold tombZ at hb; omega
            · exact h1
          have hjw : j ≤ cmpRevIdx c ki := by
            rcases h with ⟨h1, -⟩ | ⟨-, h2⟩
            · omega
            · exact h2
          have hsort : g.revs.Pairwise Rev.lt := by rw [← hg]; exact hs.gen_sorted hlt
          have hjl : j < g.revs.length := by
            rcases hjj with h' | ⟨h', -⟩
            · exact h'
            · exact absurd h' he
          -- the revision at `j` is at or below `c`
          have hjc : sint.Z (g.revs[j]'hjl).main ≤ sint.Z c := by
            unfold cmpRevIdx at hjw
            rw [← hgi, hg] at hjw
            rcases genWalk_pAbove_spec g.revs c with ⟨h1, -⟩ | ⟨m, hm, h1, h2, -⟩
            · rw [h1] at hjw; simp at hjw; omega
            · rw [h1] at hjw; simp only [Int.toNat_natCast] at hjw
              have := sorted_main_le hsort hjw hm
              omega
          have h0 : sint.Z (g.revs.headD Rev.zero).main ≤ sint.Z a := by
            have := sorted_main_le hsort (Nat.zero_le j) hjl
            have hh := headD_drop g.revs 0 (by omega)
            rw [List.drop_zero] at hh
            rw [hh]; omega
          have h0' : sint.Z ((genDrop j g).revs.headD Rev.zero).main ≤ sint.Z a := by
            rw [genDrop_revs, headD_drop _ _ hjl]; omega
          simp only [h0, h0', ↓reduceIte, Option.map_some, Nat.sub_self]
          exact ⟨by trivial, fun x hx => by cases hx; exact Nat.le_refl _⟩
  | succ t ih =>
    intro ht
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [kiFindGenAux_succ (cg := t + 1), show gi + (t + 1) + 1 = (gi + t + 1) + 1 by omega,
      kiFindGenAux_succ (cg := gi + t + 1)]
    rw [show (kiCutAt gi j ki).gens.getD (t + 1) Gen.empty = ki.gens.getD (gi + t + 1) Gen.empty by
      rw [hG, dropSet_getDs]]
    rw [hlen]
    have hiff : (t + 1 ≠ ki.gens.length - gi - 1) ↔ (gi + t + 1 ≠ ki.gens.length - 1) := by omega
    generalize ki.gens.getD (gi + t + 1) Gen.empty = g
    simp only []
    by_cases he : g.revs = []
    · simp only [he, ↓reduceIte]; exact ⟨ih1, ih2⟩
    · simp only [he, ↓reduceIte]
      by_cases ht : gi + t + 1 ≠ ki.gens.length - 1 ∧ sint.Z (g.revs.getLastD Rev.zero).main ≤ sint.Z a
      · have ht' : t + 1 ≠ ki.gens.length - gi - 1 ∧ sint.Z (g.revs.getLastD Rev.zero).main ≤ sint.Z a :=
          ⟨hiff.2 ht.1, ht.2⟩
        rw [ite_eq_left ht, ite_eq_left ht']
        exact ⟨by trivial, fun x hx => by cases hx⟩
      · have ht' : ¬ (t + 1 ≠ ki.gens.length - gi - 1 ∧ sint.Z (g.revs.getLastD Rev.zero).main ≤ sint.Z a) := by
          rw [hiff]; exact ht
        rw [ite_eq_right ht, ite_eq_right ht']
        split
        · simp only [Option.map_some, Option.some.injEq]
          refine ⟨by omega, fun x hx => by cases hx; omega⟩
        · exact ⟨ih1, ih2⟩

/-- The cut generation answers as the generation, at or above `c` (the cut at or before the walk's
stop at `c`). -/
theorem genGet_genDrop {c a : w64} (hca : sint.Z c ≤ sint.Z a) {g : Gen} {j : Nat}
    (hj : (j : Int) ≤ genWalk g.revs (pAbove c)) : genGet (genDrop j g) a = genGet g a := by
  have hca' : (j : Int) ≤ genWalk g.revs (pAbove a) := by
    have hwlt := genWalk_lt g.revs (pAbove c)
    rcases genWalk_pAbove_spec g.revs c with ⟨h1, -⟩ | ⟨m, hm, h1, h2, -⟩
    · omega
    · have := genWalk_ge (p := pAbove a) hm (by simp [pAbove]; omega)
      omega
  have hwlt := genWalk_lt g.revs (pAbove a)
  have hne : g.revs ≠ [] := by intro h; have := hca'; rw [h, genWalk_nil] at this; omega
  have hne' : (genDrop j g).revs ≠ [] := by
    rw [genDrop_revs]; intro h; have := congrArg List.length h; simp at this; omega
  unfold genGet
  rw [genDrop_revs] at hne' ⊢
  rw [genWalk_drop hca']
  simp only [hne', hne, ↓reduceIte]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  rw [List.length_drop]
  have e1 : (genWalk g.revs (pAbove a) - (j : Int)).toNat = (genWalk g.revs (pAbove a)).toNat - j := by omega
  rw [e1]
  have e2 : (List.drop j g.revs).getD ((genWalk g.revs (pAbove a)).toNat - j) Rev.zero =
      g.revs.getD (genWalk g.revs (pAbove a)).toNat Rev.zero := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
    congr 2; omega
  rw [e2]
  have e3 : ((g.revs.length - j : Nat) : Int) - (((genWalk g.revs (pAbove a)).toNat - j : Nat) : Int) - 1 =
      (g.revs.length : Int) - ((genWalk g.revs (pAbove a)).toNat : Int) - 1 := by omega
  simp only [genDrop]
  rw [e3]

/-- **A reader at or above `c` cannot tell the cut** (`kiGet`, what every read answers). -/
theorem kiGet_cutAt {ki : KeyIndex} (hs : KiS ki) {c a : w64} (hca : sint.Z c ≤ sint.Z a)
    {gi j : Nat} (h : CutLe c ki gi j) : kiGet (kiCutAt gi j ki) a = kiGet ki a := by
  have hwf := hs.wf
  obtain ⟨hgc, hlt, hjj⟩ := h.pos hwf
  have hlen : (kiCutAt gi j ki).gens.length = ki.gens.length - gi := by
    rw [kiCutAt_gens, dropSet_length]
  rw [kiGet_eq, kiGet_eq]
  unfold kiFindGen
  rw [hlen]
  obtain ⟨h1, h2⟩ := findAux_cutAt hs hca h (ki.gens.length - gi - 1) (by omega)
  rw [show ki.gens.length - gi - 1 + 1 = ki.gens.length - gi by omega] at h1
  rw [show gi + (ki.gens.length - gi - 1) + 1 = ki.gens.length by omega] at h1 h2
  rw [h1]
  cases hx : kiFindGenAux ki.gens a ki.gens.length with
  | none => rfl
  | some x =>
    have hgx := h2 x hx
    simp only [Option.map_some, Option.bind_some]
    rcases Nat.lt_or_eq_of_le hgx with hgt | heq
    · rw [show x - gi = (x - gi - 1) + 1 by omega, kiCutAt_gens, dropSet_getDs,
        show gi + (x - gi - 1) + 1 = x by omega]
    · subst heq
      rw [Nat.sub_self, kiCutAt_gens, dropSet_getD0 _ _ _ _ hlt]
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0; rw [genDrop_zero]
      · -- the scan found the cut's generation: it is `doCompact`'s at `c`
        have hgi : gi = compactGenIdx c ki.gens := by
          rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
          · exfalso
            -- the scan stops below at a generation `doCompact` steps past
            have hb := compactGenIdx_before_le c ki.gens gi h1
            obtain ⟨-, -, hnot, -⟩ := kiFindGenAux_spec ki.gens.length gi hx
            apply hnot
            refine ⟨by have := compactGenIdx_lt c ki.gens hwf.ne; omega, ?_⟩
            unfold tombZ at hb; omega
          · exact h1
        rw [genGet_genDrop hca (h.walk hwf (Int.le_refl _) hgi hj0)]

/-! ## The writer's next event on the cut -/

/-- The cut's position is in a generation of the key index, and its revision index in it. -/
def CutPos (ki : KeyIndex) (gi j : Nat) : Prop :=
  gi < ki.gens.length ∧
    (j < (ki.gens.getD gi Gen.empty).revs.length ∨ ((ki.gens.getD gi Gen.empty).revs = [] ∧ j = 0))

theorem CutLe.cutPos {c : w64} {ki : KeyIndex} (hwf : KiWf ki) {gi j : Nat} (h : CutLe c ki gi j) :
    CutPos ki gi j :=
  ⟨(h.pos hwf).2.1, (h.pos hwf).2.2⟩

theorem genDrop_genPut {j : Nat} {g : Gen} (hj : j < g.revs.length ∨ (g.revs = [] ∧ j = 0))
    (rev : Rev) : genDrop j (genPut g rev) = genPut (genDrop j g) rev := by
  rcases hj with hj | ⟨-, rfl⟩
  · have hne : g.revs ≠ [] := by intro h; rw [h] at hj; simp at hj
    have hne' : g.revs.drop j ≠ [] := by
      intro h; have := congrArg List.length h; simp at this; omega
    unfold genDrop genPut
    simp only [hne, hne', ↓reduceIte, List.drop_append_of_le_length (Nat.le_of_lt hj)]
  · rw [genDrop_zero, genDrop_zero]

theorem cutPos_ne {ki : KeyIndex} {gi j : Nat} (h : CutPos ki gi j) : ki.gens ≠ [] := by
  intro he; have := h.1; rw [he] at this; simp at this

theorem kiCutAt_gens_ne {ki : KeyIndex} {gi j : Nat} (h : CutPos ki gi j) : (kiCutAt gi j ki).gens ≠ [] := by
  intro he; have := congrArg List.length he; rw [kiCutAt_gens, dropSet_length] at this
  simp at this; have := h.1; omega

theorem kiCutAt_getLastD {ki : KeyIndex} {gi j : Nat} (h : CutPos ki gi j) :
    (kiCutAt gi j ki).gens.getLastD Gen.empty =
      if gi + 1 = ki.gens.length then genDrop j (ki.gens.getD gi Gen.empty)
      else ki.gens.getLastD Gen.empty := by
  have hne := cutPos_ne h
  have hlt := h.1
  have hne' := kiCutAt_gens_ne h
  rw [getLastD_eq_getD _ _ hne', getLastD_eq_getD _ _ hne, kiCutAt_gens, dropSet_length]
  split
  · rw [show ki.gens.length - gi - 1 = 0 by omega, dropSet_getD0 _ _ _ _ hlt]
  · rw [show ki.gens.length - gi - 1 = (ki.gens.length - gi - 2) + 1 by omega, dropSet_getDs]
    congr 1; omega

/-- The cut keeps the last generation's emptiness (`tombstone`'s test). -/
theorem kiLastEmpty_cutAt {ki : KeyIndex} {gi j : Nat} (h : CutPos ki gi j) :
    kiLastEmpty (kiCutAt gi j ki) = kiLastEmpty ki := by
  unfold kiLastEmpty
  rw [kiCutAt_getLastD h]
  split
  · rename_i hl
    rw [getLastD_eq_getD _ _ (cutPos_ne h), show ki.gens.length - 1 = gi by omega]
    simp only [decide_eq_decide]
    exact genDrop_revs_ne h.2
  · rfl

theorem kiCutAt_kiPut {ki : KeyIndex} {gi j : Nat} (h : CutPos ki gi j) (rev : Rev) :
    kiCutAt gi j (kiPut ki rev) = kiPut (kiCutAt gi j ki) rev := by
  have hne := cutPos_ne h
  have hlt := h.1
  have hne' := kiCutAt_gens_ne h
  refine KeyIndex.ext' rfl ?_
  rw [kiCutAt_gens, kiPut_gens_of_ne hne, kiPut_gens_of_ne hne', kiCutAt_getLastD h, kiCutAt_gens]
  split
  · rename_i hlast
    have hgi : gi = ki.gens.length - 1 := by omega
    rw [hgi, getD_dropLast_append_last _ _ _ hne, ← genDrop_genPut (by rw [← hgi]; exact h.2),
      getLastD_eq_getD _ _ hne]
    apply List.ext_getElem?
    intro t
    simp only [List.getElem?_drop, List.getElem?_set, List.length_drop, List.length_set,
      getElem?_dropLast_append _ _ hne, List.getElem?_append, List.length_dropLast, List.length_append,
      List.length_singleton, List.getElem?_singleton]
    grind
  · rename_i hlast
    rw [getD_dropLast_append_lt _ _ _ _ (by omega)]
    exact dropSet_dropLast_append _ _ _ _ (by omega)

theorem kiCutAt_appendEmpty {ki : KeyIndex} {gi j : Nat} (hlt : gi < ki.gens.length) :
    kiCutAt gi j { ki with gens := ki.gens ++ [Gen.empty] } =
      { kiCutAt gi j ki with gens := (kiCutAt gi j ki).gens ++ [Gen.empty] } := by
  refine KeyIndex.ext' rfl ?_
  show (kiCutAt gi j { ki with gens := ki.gens ++ [Gen.empty] }).gens = (kiCutAt gi j ki).gens ++ [Gen.empty]
  rw [kiCutAt_gens, kiCutAt_gens]
  simp only
  rw [getD_append_lt _ _ _ _ hlt]
  apply List.ext_getElem?
  intro t
  simp only [List.getElem?_drop, List.getElem?_set, List.length_drop, List.length_set,
    List.getElem?_append, List.length_append, List.length_singleton]
  grind

theorem kiCutAt_kiTombstone {ki : KeyIndex} {gi j : Nat} (h : CutPos ki gi j) (rev : Rev) :
    kiCutAt gi j (kiTombstone ki rev) = kiTombstone (kiCutAt gi j ki) rev := by
  have hne := cutPos_ne h
  have hput : CutPos (kiPut ki rev) gi j := by
    refine ⟨by rw [kiPut_gens_of_ne hne, length_dropLast_append _ _ hne]; exact h.1, ?_⟩
    rw [kiPut_gens_of_ne hne]
    by_cases hl : gi < ki.gens.length - 1
    · rw [getD_dropLast_append_lt _ _ _ _ hl]; exact h.2
    · rw [show gi = ki.gens.length - 1 by have := h.1; omega, getD_dropLast_append_last _ _ _ hne,
        genPut_revs]
      left
      rcases h.2 with h2 | ⟨-, rfl⟩
      · rw [getLastD_eq_getD _ _ hne, show ki.gens.length - 1 = gi by have := h.1; omega,
          List.length_append, List.length_singleton]
        omega
      · simp
  have h1 : kiTombstone ki rev = { kiPut ki rev with gens := (kiPut ki rev).gens ++ [Gen.empty] } := rfl
  have h2 : kiTombstone (kiCutAt gi j ki) rev =
      { kiPut (kiCutAt gi j ki) rev with gens := (kiPut (kiCutAt gi j ki) rev).gens ++ [Gen.empty] } := rfl
  rw [h1, h2, kiCutAt_appendEmpty hput.1, kiCutAt_kiPut h rev]

/-- The writer's next event on a key's index, as `treeIndex.Put`/`Tombstone` apply it to what the
tree has of the key (`o`): a put to the key's index, or to a fresh one; a tombstone to it unless its
last generation is empty (`ErrRevisionNotFound`), nothing to an absent key. -/
def stepO (ev : Ev) (o : Option KeyIndex) : Option KeyIndex :=
  match o with
  | some ki' =>
    if ev.tomb then (if kiLastEmpty ki' then some ki' else some (kiTombstone ki' ev.rev))
    else some (kiPut ki' ev.rev)
  | none => if ev.tomb then none else some (kiPut KeyIndex.fresh ev.rev)

/-- The index's step, key by key. -/
theorem idxGet_idxApply {idx : IndexM} (hs : idx.Pairwise idxLess) (ev : Ev) (k : GoString) :
    idxGet (idxApply idx ev) k = if ev.key = k then stepO ev (idxGet idx k) else idxGet idx k := by
  unfold idxApply
  by_cases ht : ev.tomb = true
  · simp only [ht, ↓reduceIte]
    unfold idxTombstone
    cases hg : idxGet idx ev.key with
    | none =>
      by_cases hk : ev.key = k
      · subst hk; simp [hg, stepO, ht]
      · simp [hk]
    | some ki =>
      by_cases hle : kiLastEmpty ki = true
      · simp only [hle, ↓reduceIte]
        by_cases hk : ev.key = k
        · subst hk; simp [hg, stepO, ht, hle]
        · simp [hk]
      · simp only [hle, Bool.false_eq_true, ↓reduceIte]
        rw [idxGet_btInsert hs]
        by_cases hk : ev.key = k
        · subst hk; simp [hg, stepO, ht, hle]
        · simp [hk]
  · simp only [ht, Bool.false_eq_true, ↓reduceIte]
    unfold idxPut
    cases hg : idxGet idx ev.key with
    | none =>
      simp only
      rw [idxGet_btInsert hs]
      by_cases hk : ev.key = k
      · subst hk; simp [hg, stepO, ht]
      · simp [hk]
    | some ki =>
      simp only
      rw [idxGet_btInsert hs]
      by_cases hk : ev.key = k
      · subst hk; simp [hg, stepO, ht]
      · simp [hk]

theorem idxApply_sorted {idx : IndexM} (hs : idx.Pairwise idxLess) (ev : Ev) :
    (idxApply idx ev).Pairwise idxLess := by
  unfold idxApply
  split
  · unfold idxTombstone
    split
    · split
      · exact hs
      · exact btInsert_sorted idxLess_swo hs
    · exact hs
  · unfold idxPut
    split
    · exact btInsert_sorted idxLess_swo hs
    · exact btInsert_sorted idxLess_swo hs

/-- The cut position survives an event above `c`. -/
theorem CutLe.kiApply {c : w64} {ki : KeyIndex} (hwf : KiWf ki) {gi j : Nat} (h : CutLe c ki gi j)
    (ev : Ev) (hc : sint.Z c < sint.Z ev.rev.main) : CutLe c (kiApply ki ev) gi j := by
  have hne := hwf.ne
  have hlt := compactGenIdx_lt c ki.gens hne
  -- a put: the generations' choice and the walk are unchanged
  have hput : ∀ rev : Rev, sint.Z c < sint.Z rev.main → CutLe c (kiPut ki rev) gi j := by
    intro rev hcr
    have hidx : compactGenIdx c (kiPut ki rev).gens = compactGenIdx c ki.gens := by
      rw [kiPut_gens_of_ne hne]; exact compactGenIdx_put hwf c rev hcr
    have hgd : ∀ i, i < ki.gens.length →
        ((kiPut ki rev).gens.getD i Gen.empty).revs.length ≥ (ki.gens.getD i Gen.empty).revs.length ∧
        genWalk ((kiPut ki rev).gens.getD i Gen.empty).revs (pAbove c) =
          genWalk (ki.gens.getD i Gen.empty).revs (pAbove c) := by
      intro i hi
      rw [kiPut_gens_of_ne hne]
      by_cases hl : i < ki.gens.length - 1
      · rw [getD_dropLast_append_lt _ _ _ _ hl]; exact ⟨Nat.le_refl _, rfl⟩
      · rw [show i = ki.gens.length - 1 by omega, getD_dropLast_append_last _ _ _ hne, genPut_revs,
          genWalk_append_true _ _ _ (by simp [pAbove]; omega), getLastD_eq_getD _ _ hne]
        simp
    have hcmp : cmpRevIdx c (kiPut ki rev) = cmpRevIdx c ki := by
      unfold cmpRevIdx; rw [hidx, (hgd _ hlt).2]
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; rw [hidx]; exact ⟨h1, by have := (hgd gi (by omega)).1; omega⟩
    · right; rw [hidx, hcmp]; exact ⟨h1, h2⟩
  unfold mvcc.kiApply
  split
  · split
    · exact h
    · -- a tombstone: a put, and an empty generation after one whose tombstone is above `c`
      have hp := hput ev.rev hc
      have hpne := (hwf.put ev.rev).ne
      have hlast : ¬ tombZ ((kiPut ki ev.rev).gens.getLastD Gen.empty) < sint.Z c := by
        rw [kiPut_gens_of_ne hne, getLastD_append_singleton]
        unfold tombZ
        rw [genPut_revs, List.getLastD_eq_getLast?, List.getLast?_append, List.getLast?_singleton]
        all_goals first | omega | (simp; omega)
      have hidx : compactGenIdx c (kiTombstone ki ev.rev).gens = compactGenIdx c (kiPut ki ev.rev).gens := by
        rw [kiTombstone_gens]; exact compactGenIdx_appendEmpty hpne c hlast
      have hlt' := compactGenIdx_lt c (kiPut ki ev.rev).gens hpne
      have hcmp : cmpRevIdx c (kiTombstone ki ev.rev) = cmpRevIdx c (kiPut ki ev.rev) := by
        unfold cmpRevIdx; rw [hidx, kiTombstone_gens, getD_append_lt _ _ _ _ hlt']
      rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left; rw [hidx, kiTombstone_gens, getD_append_lt _ _ _ _ (by omega)]; exact ⟨h1, h2⟩
      · right; rw [hidx, hcmp]; exact ⟨h1, h2⟩
  · exact hput ev.rev hc

/-- **The cut commutes with the writer's next event** (above `c`). -/
theorem kiCutO_step {c : w64} {ki : KeyIndex} (hwf : KiWf ki) {gi j : Nat} (h : CutLe c ki gi j)
    (ev : Ev) : kiCutO gi j (kiApply ki ev) = stepO ev (kiCutO gi j ki) := by
  have hp := h.cutPos hwf
  unfold kiCutO
  by_cases hE : kiIsEmpty (kiCutAt gi j ki) = true
  · -- the cut is empty: the last generation, empty
    have hle : kiLastEmpty ki = true := by
      rw [← kiLastEmpty_cutAt hp]; exact kiIsEmpty_lastEmpty hE
    rw [ite_eq_left hE]
    unfold stepO mvcc.kiApply
    by_cases ht : ev.tomb = true
    · simp only [ht, hle, ↓reduceIte, hE]
    · simp only [ht, Bool.false_eq_true, ↓reduceIte]
      rw [kiCutAt_kiPut hp, kiIsEmpty_kiPut]
      simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
      -- the cut's one generation is the last, empty, version `0`
      unfold kiIsEmpty at hE
      split at hE
      · rename_i x hx
        simp only [decide_eq_true_eq] at hE
        have hgi : gi + 1 = ki.gens.length := by
          have := congrArg List.length hx; rw [kiCutAt_gens, dropSet_length] at this; simp at this; omega
        have hx0 : x = genDrop j (ki.gens.getD gi Gen.empty) := by
          have := kiCutAt_getLastD hp; rw [hx, ite_eq_left hgi] at this; simpa using this
        have hrevs : (ki.gens.getD gi Gen.empty).revs = [] := by
          rw [← genDrop_revs_ne hp.2, ← hx0]; exact hE
        have hver : x.ver = W64 0 := by
          rw [hx0]
          show (ki.gens.getD gi Gen.empty).ver = W64 0
          have hw := hwf.gens (ki.gens.getD gi Gen.empty) (by rw [getD_lt _ hp.1]; exact List.getElem_mem hp.1)
          rw [hw.1, hrevs]; rfl
        refine KeyIndex.ext' rfl ?_
        rw [kiPut_gens, kiPut_gens, hx]
        simp [gensOrEmpty, genPut, hE, hver, Gen.empty, KeyIndex.fresh]
      · cases hE
  · rw [ite_eq_right hE]
    unfold stepO mvcc.kiApply
    by_cases ht : ev.tomb = true
    · simp only [ht, ↓reduceIte, kiLastEmpty_cutAt hp]
      by_cases hle : kiLastEmpty ki = true
      · simp only [hle, ↓reduceIte]
        rw [ite_eq_right hE]
      · simp only [hle, Bool.false_eq_true, ↓reduceIte]
        rw [kiCutAt_kiTombstone hp, kiIsEmpty_kiTombstone]
        rfl
    · simp only [ht, Bool.false_eq_true, ↓reduceIte]
      rw [kiCutAt_kiPut hp, kiIsEmpty_kiPut]
      rfl

/-! ## Key indexes up to the unread header of a tombstone-only generation -/

/-- **A generation's unread header cleared**: a generation with one revision gets `created := 0`,
`ver := 1`, the values `restoreTombstone` gives it. Applied to the generations that are not the last
(`kiNorm`), whose one revision is their tombstone: `kiGet` never answers it (`kiGet_kiNorm`), and
compaction and `keep` read only revisions. -/
def genNorm (g : Gen) : Gen :=
  if g.revs.length = 1 then { g with created := W64 0, ver := W64 1 } else g

/-- **A key index up to the unread headers**: every generation but the last normalized. -/
def kiNorm (ki : KeyIndex) : KeyIndex :=
  { ki with gens := ki.gens.dropLast.map genNorm ++ ki.gens.getLast?.toList }

theorem genNorm_revs (g : Gen) : (genNorm g).revs = g.revs := by
  unfold genNorm; split <;> rfl

theorem genNorm_idem (g : Gen) : genNorm (genNorm g) = genNorm g := by
  unfold genNorm
  split <;> simp_all

theorem kiNorm_modified (ki : KeyIndex) : (kiNorm ki).modified = ki.modified := rfl

theorem kiNorm_nil {ki : KeyIndex} (h : ki.gens = []) : kiNorm ki = ki := by
  refine KeyIndex.ext' rfl ?_
  simp [kiNorm, h]

theorem kiNorm_gens_ne {ki : KeyIndex} (h : ki.gens ≠ []) :
    (kiNorm ki).gens = ki.gens.dropLast.map genNorm ++ [ki.gens.getLastD Gen.empty] := by
  unfold kiNorm
  simp only
  rw [List.getLast?_eq_some_getLast h, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast h]
  rfl

theorem kiNorm_length (ki : KeyIndex) : (kiNorm ki).gens.length = ki.gens.length := by
  by_cases h : ki.gens = []
  · rw [kiNorm_nil h]
  · rw [kiNorm_gens_ne h]
    simp only [List.length_append, List.length_map, List.length_dropLast, List.length_singleton]
    have := List.length_pos_iff.2 h; omega

theorem kiNorm_getD (ki : KeyIndex) (i : Nat) :
    (kiNorm ki).gens.getD i Gen.empty =
      if i + 1 < ki.gens.length then genNorm (ki.gens.getD i Gen.empty) else ki.gens.getD i Gen.empty := by
  by_cases h : ki.gens = []
  · rw [kiNorm_nil h]; simp [h]
  · have hpos := List.length_pos_iff.2 h
    rw [kiNorm_gens_ne h]
    split
    · rename_i hi
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp; omega), List.getElem?_map,
        List.getElem?_dropLast, ite_eq_left (by omega), List.getD_eq_getElem?_getD]
      cases ki.gens[i]? <;> rfl
    · rename_i hi
      by_cases hl : i = ki.gens.length - 1
      · subst hl
        have := getD_dropLast_append_last (ki.gens.dropLast.map genNorm ++ [ki.gens.getLastD Gen.empty])
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp),
          getLastD_eq_getD _ _ h]
        simp
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega),
          List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]

theorem kiNorm_revs (ki : KeyIndex) (i : Nat) :
    ((kiNorm ki).gens.getD i Gen.empty).revs = (ki.gens.getD i Gen.empty).revs := by
  rw [kiNorm_getD]; split
  · exact genNorm_revs _
  · rfl

theorem kiNorm_getLastD (ki : KeyIndex) :
    (kiNorm ki).gens.getLastD Gen.empty = ki.gens.getLastD Gen.empty := by
  by_cases h : ki.gens = []
  · rw [kiNorm_nil h]
  · rw [kiNorm_gens_ne h, getLastD_append_singleton]

theorem kiNorm_map_revs (ki : KeyIndex) : (kiNorm ki).gens.map Gen.revs = ki.gens.map Gen.revs := by
  by_cases h : ki.gens = []
  · rw [kiNorm_nil h]
  · rw [kiNorm_gens_ne h]
    conv => rhs; rw [← List.dropLast_concat_getLast h]
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
    congr 1
    · apply List.map_congr_left; intro g _; exact genNorm_revs g
    · rw [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast h]; rfl

/-- Lists of the same length, equal at every index. -/
theorem list_ext_getD {α : Type} {l l' : List α} (d : α) (hl : l.length = l'.length)
    (h : ∀ i, i < l.length → l.getD i d = l'.getD i d) : l = l' := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < l.length
  · have hi' : i < l'.length := hl ▸ hi
    have := h i hi
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hi'] at this
    rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi']
    simpa using this
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- **Two key indexes the same up to the unread headers.** -/
theorem kiNorm_eq_of {A B : KeyIndex} (hm : A.modified = B.modified) (hl : A.gens.length = B.gens.length)
    (hg : ∀ i, i + 1 < A.gens.length → genNorm (A.gens.getD i Gen.empty) = genNorm (B.gens.getD i Gen.empty))
    (hlast : A.gens.getLastD Gen.empty = B.gens.getLastD Gen.empty) : kiNorm A = kiNorm B := by
  refine KeyIndex.ext' hm (list_ext_getD Gen.empty (by rw [kiNorm_length, kiNorm_length, hl]) ?_)
  intro i hi
  rw [kiNorm_length] at hi
  rw [kiNorm_getD, kiNorm_getD]
  by_cases h1 : i + 1 < A.gens.length
  · rw [ite_eq_left h1, ite_eq_left (by omega)]; exact hg i h1
  · rw [ite_eq_right h1, ite_eq_right (by omega)]
    have hA : A.gens ≠ [] := by intro h; rw [h] at hi; simp at hi
    have hB : B.gens ≠ [] := by intro h; rw [h, List.length_nil] at hl; omega
    rw [getLastD_eq_getD _ _ hA, getLastD_eq_getD _ _ hB] at hlast
    rw [show i = A.gens.length - 1 by omega, hlast, hl]

theorem kiNorm_idem (ki : KeyIndex) : kiNorm (kiNorm ki) = kiNorm ki := by
  refine kiNorm_eq_of (by rfl) (kiNorm_length ki) ?_ ?_
  · intro i hi
    rw [kiNorm_length] at hi
    rw [kiNorm_getD, ite_eq_left (by omega), genNorm_idem]
  · exact kiNorm_getLastD ki

/-! ### What reads the key index sees no difference -/

theorem kiFindGenAux_congrRevs (gens gens' : List Gen) (a : w64) (hl : gens.length = gens'.length)
    (hr : ∀ i, (gens.getD i Gen.empty).revs = (gens'.getD i Gen.empty).revs) :
    ∀ n, kiFindGenAux gens a n = kiFindGenAux gens' a n
  | 0 => rfl
  | n + 1 => by
    rw [kiFindGenAux_succ, kiFindGenAux_succ]
    simp only [hr n, hl, kiFindGenAux_congrRevs gens gens' a hl hr n]

theorem kiFindGen_kiNorm (ki : KeyIndex) (a : w64) : kiFindGen (kiNorm ki) a = kiFindGen ki a := by
  unfold kiFindGen
  rw [kiNorm_length]
  exact kiFindGenAux_congrRevs _ _ a (kiNorm_length ki) (kiNorm_revs ki) _

/-- **Readers see no difference** (`kiGet`, what every read of the index answers): the scan never
stops at a generation that is not the last and has one revision (its tombstone, at or below every
revision the scan could stop there for), the only ones `kiNorm` changes. -/
theorem kiGet_kiNorm (ki : KeyIndex) (a : w64) : kiGet (kiNorm ki) a = kiGet ki a := by
  unfold kiGet
  rw [kiFindGen_kiNorm]
  cases hf : kiFindGen ki a with
  | none => rfl
  | some gx =>
    obtain ⟨hlt, hne, hnot, hhead⟩ := kiFindGenAux_spec ki.gens.length gx hf
    simp only
    have hg : (kiNorm ki).gens.getD gx Gen.empty = ki.gens.getD gx Gen.empty := by
      rw [kiNorm_getD]
      split
      · rename_i hl
        unfold genNorm
        split
        · rename_i h1
          exfalso
          apply hnot
          refine ⟨by omega, ?_⟩
          generalize ki.gens.getD gx Gen.empty = g at *
          match g, h1 with
          | ⟨_, _, [r]⟩, _ => simpa using hhead
        · rfl
      · rfl
    rw [hg]

theorem genAdv_congrRevs (c : w64) {g g' h h' : Gen} (h1 : g.revs = h.revs) (h2 : g'.revs = h'.revs) :
    genAdv c g g' = genAdv c h h' := by
  unfold genAdv tombZ genRecreatedAt
  rw [h1, h2]

theorem compactGenIdx_congrRevs (c : w64) :
    ∀ (G G' : List Gen), G.map Gen.revs = G'.map Gen.revs → compactGenIdx c G = compactGenIdx c G'
  | [], [], _ => rfl
  | [_], [_], _ => rfl
  | g :: g' :: gs, h :: h' :: hs, he => by
    simp only [List.map_cons, List.cons.injEq] at he
    unfold compactGenIdx
    rw [genAdv_congrRevs c he.1 he.2.1,
      compactGenIdx_congrRevs c (g' :: gs) (h' :: hs) (by simp [he.2.1, he.2.2])]
  | [], _ :: _, he => by simp at he
  | _ :: _, [], he => by simp at he
  | [_], _ :: _ :: _, he => by simp at he
  | _ :: _ :: _, [_], he => by simp at he

theorem compactGenIdx_kiNorm (c : w64) (ki : KeyIndex) :
    compactGenIdx c (kiNorm ki).gens = compactGenIdx c ki.gens :=
  compactGenIdx_congrRevs c _ _ (kiNorm_map_revs ki)

theorem kiAvail_kiNorm (c : w64) (ki : KeyIndex) : kiAvail c (kiNorm ki) = kiAvail c ki := by
  unfold kiAvail
  simp only []
  rw [compactGenIdx_kiNorm, kiNorm_revs]

theorem kiIsEmpty_eq (ki : KeyIndex) :
    kiIsEmpty ki = decide (ki.gens.length = 1 ∧ (ki.gens.getLastD Gen.empty).revs = []) := by
  unfold kiIsEmpty
  split
  · rename_i g hg; rw [hg]; simp
  · rename_i hg
    symm
    rw [decide_eq_false_iff_not]
    rintro ⟨h1, -⟩
    match hgs : ki.gens, h1 with
    | [g], _ => exact hg g hgs

theorem kiIsEmpty_kiNorm (ki : KeyIndex) : kiIsEmpty (kiNorm ki) = kiIsEmpty ki := by
  rw [kiIsEmpty_eq, kiIsEmpty_eq, kiNorm_length, kiNorm_getLastD]

theorem kiLastEmpty_kiNorm (ki : KeyIndex) : kiLastEmpty (kiNorm ki) = kiLastEmpty ki := by
  unfold kiLastEmpty; rw [kiNorm_getLastD]

theorem kiKeep_kiNorm (c : w64) (ki : KeyIndex) : kiKeep c (kiNorm ki) = kiKeep c ki := by
  unfold kiKeep
  rw [kiIsEmpty_kiNorm]
  simp only []
  rw [compactGenIdx_kiNorm, kiNorm_revs, kiNorm_length]

theorem gensOk_kiNorm (ki : KeyIndex) :
    ((kiNorm ki).gens ≠ [] ∧ ∀ i, i + 1 < (kiNorm ki).gens.length → ((kiNorm ki).gens.getD i Gen.empty).revs ≠ []) ↔
      (ki.gens ≠ [] ∧ ∀ i, i + 1 < ki.gens.length → (ki.gens.getD i Gen.empty).revs ≠ []) := by
  rw [kiNorm_length]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => h1 (by rw [kiNorm_nil h]; exact h), fun i hi => ?_⟩
    rw [← kiNorm_revs]; exact h2 i hi
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => h1 (by
      have := kiNorm_length ki; rw [h] at this; simp at this
      exact List.length_eq_zero_iff.1 this.symm), fun i hi => ?_⟩
    rw [kiNorm_revs]; exact h2 i hi

theorem kiRevs_kiNorm (ki : KeyIndex) : kiRevs (kiNorm ki) = kiRevs ki := by
  unfold kiRevs; rw [kiNorm_map_revs]

/-! ### The writer's steps and compaction, up to the headers -/

theorem kiNorm_kiPut (ki : KeyIndex) (rev : Rev) :
    kiNorm (kiPut (kiNorm ki) rev) = kiNorm (kiPut ki rev) := by
  by_cases h : ki.gens = []
  · rw [kiNorm_nil h]
  have hn : (kiNorm ki).gens ≠ [] := by
    intro he; have := kiNorm_length ki; rw [he] at this; simp at this
    exact h (List.length_eq_zero_iff.1 this.symm)
  refine kiNorm_eq_of (by rfl) ?_ ?_ ?_
  · rw [kiPut_gens_of_ne hn, kiPut_gens_of_ne h, length_dropLast_append _ _ hn,
      length_dropLast_append _ _ h, kiNorm_length]
  · intro i hi
    rw [kiPut_gens_of_ne hn, length_dropLast_append _ _ hn, kiNorm_length] at hi
    rw [kiPut_gens_of_ne hn, kiPut_gens_of_ne h, getD_dropLast_append_lt _ _ _ _ (by rw [kiNorm_length]; omega),
      getD_dropLast_append_lt _ _ _ _ (by omega), kiNorm_getD, ite_eq_left hi, genNorm_idem]
  · rw [kiPut_gens_of_ne hn, kiPut_gens_of_ne h, getLastD_append_singleton, getLastD_append_singleton,
      kiNorm_getLastD]

theorem kiNorm_kiTombstone (ki : KeyIndex) (rev : Rev) :
    kiNorm (kiTombstone (kiNorm ki) rev) = kiNorm (kiTombstone ki rev) := by
  by_cases h : ki.gens = []
  · rw [kiNorm_nil h]
  have hn : (kiNorm ki).gens ≠ [] := by
    intro he; have := kiNorm_length ki; rw [he] at this; simp at this
    exact h (List.length_eq_zero_iff.1 this.symm)
  refine kiNorm_eq_of (by rfl) ?_ ?_ ?_
  · simp only [kiTombstone_gens, kiPut_gens_of_ne hn, kiPut_gens_of_ne h, List.length_append,
      List.length_dropLast, List.length_singleton, kiNorm_length]
  · intro i hi
    rw [kiTombstone_gens, kiPut_gens_of_ne hn, List.length_append, length_dropLast_append _ _ hn,
      kiNorm_length] at hi
    simp only [List.length_singleton] at hi
    rw [kiTombstone_gens, kiTombstone_gens, getD_append_lt _ _ _ _ (by
        rw [kiPut_gens_of_ne hn, length_dropLast_append _ _ hn, kiNorm_length]; omega),
      getD_append_lt _ _ _ _ (by rw [kiPut_gens_of_ne h, length_dropLast_append _ _ h]; omega),
      kiPut_gens_of_ne hn, kiPut_gens_of_ne h]
    by_cases hl : i < ki.gens.length - 1
    · rw [getD_dropLast_append_lt _ _ _ _ (by rw [kiNorm_length]; omega),
        getD_dropLast_append_lt _ _ _ _ hl, kiNorm_getD, ite_eq_left (by omega), genNorm_idem]
    · have hi' : i = ki.gens.length - 1 := by omega
      rw [hi']
      have e := getD_dropLast_append_last (kiNorm ki).gens (genPut ((kiNorm ki).gens.getLastD Gen.empty) rev)
        Gen.empty hn
      rw [kiNorm_length] at e
      rw [e, getD_dropLast_append_last _ _ _ h, kiNorm_getLastD]
  · rw [kiTombstone_gens, kiTombstone_gens, getLastD_append_singleton, getLastD_append_singleton]

theorem cutGen_header (c : w64) (g : Gen) (a b : w64) :
    cutGen c { g with created := a, ver := b } = { cutGen c g with created := a, ver := b } := by
  unfold cutGen; simp only; split <;> rfl

theorem genNorm_cutGen_genNorm (c : w64) (g : Gen) :
    genNorm (cutGen c (genNorm g)) = genNorm (cutGen c g) := by
  by_cases h1 : g.revs.length = 1
  · have hn : genNorm g = { g with created := W64 0, ver := W64 1 } := by unfold genNorm; rw [ite_eq_left h1]
    rw [hn, cutGen_header]
    have hl : (cutGen c g).revs.length = 1 := by
      rcases cutGen_cases c g with h | ⟨j, hj, -, -, hr, -⟩
      · rw [h]; exact h1
      · rw [hr, List.length_drop]; omega
    unfold genNorm
    simp only [hl, ↓reduceIte]
  · have hn : genNorm g = g := by unfold genNorm; rw [ite_eq_right h1]
    rw [hn]

theorem kiCompact_getLastD' {ki : KeyIndex} (hne : ki.gens ≠ []) (c : w64) :
    (kiCompact c ki).gens.getLastD Gen.empty =
      if compactGenIdx c ki.gens + 1 = ki.gens.length then
        cutGen c (ki.gens.getD (compactGenIdx c ki.gens) Gen.empty)
      else ki.gens.getLastD Gen.empty := by
  have hlt := compactGenIdx_lt c ki.gens hne
  have hG := kiCompact_gens c ki
  generalize compactGenIdx c ki.gens = gi at *
  have hne' : (kiCompact c ki).gens ≠ [] := by
    intro h; have := congrArg List.length h; rw [hG, dropSet_length] at this; simp at this; omega
  rw [getLastD_eq_getD _ _ hne', getLastD_eq_getD _ _ hne, hG, dropSet_length]
  split
  · rw [show ki.gens.length - gi - 1 = 0 by omega, dropSet_getD0 _ _ _ _ hlt]
  · rw [show ki.gens.length - gi - 1 = (ki.gens.length - gi - 2) + 1 by omega, dropSet_getDs]
    congr 1; omega

theorem kiNorm_kiCompact (c : w64) (ki : KeyIndex) :
    kiNorm (kiCompact c (kiNorm ki)) = kiNorm (kiCompact c ki) := by
  by_cases h : ki.gens = []
  · rw [kiNorm_nil h]
  have hn : (kiNorm ki).gens ≠ [] := by
    intro he; have := kiNorm_length ki; rw [he] at this; simp at this
    exact h (List.length_eq_zero_iff.1 this.symm)
  have hlt := compactGenIdx_lt c ki.gens h
  have hidx := compactGenIdx_kiNorm c ki
  refine kiNorm_eq_of (by rfl) ?_ ?_ ?_
  · rw [kiCompact_gens, kiCompact_gens, dropSet_length, dropSet_length, hidx, kiNorm_length]
  · intro t ht
    rw [kiCompact_gens, dropSet_length, hidx, kiNorm_length] at ht
    rw [kiCompact_gens, kiCompact_gens, hidx]
    cases t with
    | zero =>
      rw [dropSet_getD0 _ _ _ _ (by rw [kiNorm_length]; exact hlt), dropSet_getD0 _ _ _ _ hlt,
        kiNorm_getD, ite_eq_left (by omega), genNorm_cutGen_genNorm]
    | succ t =>
      rw [dropSet_getDs, dropSet_getDs, kiNorm_getD, ite_eq_left (by omega), genNorm_idem]
  · rw [kiCompact_getLastD' hn, kiCompact_getLastD' h, hidx, kiNorm_length, kiNorm_getD, kiNorm_getLastD]
    split
    · rename_i hl; rw [ite_eq_right (by omega)]
    · rfl

/-- The writer's step on what the tree has of a key, up to the headers. -/
theorem stepO_norm (ev : Ev) {o o' : Option KeyIndex} (h : o.map kiNorm = o'.map kiNorm) :
    (stepO ev o).map kiNorm = (stepO ev o').map kiNorm := by
  match o, o', h with
  | none, none, _ => rfl
  | some X, some Y, h =>
    simp only [Option.map_some, Option.some.injEq] at h
    have hle : kiLastEmpty X = kiLastEmpty Y := by
      rw [← kiLastEmpty_kiNorm X, h, kiLastEmpty_kiNorm]
    simp only [stepO]
    rw [hle]
    split
    · split
      · simp [h]
      · simp only [Option.map_some, Option.some.injEq]
        rw [← kiNorm_kiTombstone X, h, kiNorm_kiTombstone]
    · simp only [Option.map_some, Option.some.injEq]
      rw [← kiNorm_kiPut X, h, kiNorm_kiPut]

/-! ## The index: every key cut at a full revision of its own -/

/-- **The index holds the events `evs`, each key cut at a full revision of its own** (up to the
unread headers): for every key, a level `c` with `-1 ≤ c ≤ cmax` and a revision of the key at or
before the one compaction at `c` keeps (`CutLe`), the tree's key index being the log's with every
revision before that one dropped (`kiCutAt`), absent if that leaves nothing (`kiCutO`); equal up to
the header of a tombstone-only generation that is not the last (`kiNorm`). A compaction at `c` is
the cut at the revision it keeps (`IdxCRepN_of`); `restore()` over a bucket a compaction job thinned
cuts at each key's first surviving revision (`InvIndexRestore.lean`'s `idxRestore_cut`). The lock's
invariant (`idxLockInv`'s `HL`). -/
def IdxCRepN (cmax : Int) (evs : List Ev) (idx : IndexM) : Prop :=
  idx.Pairwise idxLess ∧
    ∀ k, ∃ c : Int, -1 ≤ c ∧ c ≤ cmax ∧ ∃ gi j, CutLe (W64 c) (kiOfKey evs k) gi j ∧
      (idxGet idx k).map kiNorm = (kiCutO gi j (kiOfKey evs k)).map kiNorm

/-- Each key compacted at a level of its own (`IdxCRep`, the private index's) gives it. -/
theorem IdxCRepN_of {cmax : Int} {evs : List Ev} {idx : IndexM} (h : IdxCRep cmax evs idx) :
    IdxCRepN cmax evs idx :=
  ⟨h.1, fun k => by
    obtain ⟨c, h0, h1, h2⟩ := h.2 k
    exact ⟨c, h0, h1, _, _, CutLe.cmp _ _, by rw [h2, kiCompactO_eq_cutO]⟩⟩

theorem IdxCRepN.nil {cmax : Int} (h : -1 ≤ cmax) : IdxCRepN cmax [] [] := IdxCRepN_of (IdxCRep.nil h)

theorem IdxCRepN.mono {cmax cmax' : Int} {evs : List Ev} {idx : IndexM} (h : IdxCRepN cmax evs idx)
    (hle : cmax ≤ cmax') : IdxCRepN cmax' evs idx :=
  ⟨h.1, fun k => by
    obtain ⟨c, h0, h1, h2⟩ := h.2 k
    exact ⟨c, h0, Int.le_trans h1 hle, h2⟩⟩

theorem kiOfKey_wf (evs : List Ev) (k : GoString) : KiWf (kiOfKey evs k) := (kiOfKey_struct k evs).1

/-- A key the index has: its key index is the cut, up to the headers, and the cut is not empty. -/
theorem IdxCRepN.get_some {cmax : Int} {evs : List Ev} {idx : IndexM} (h : IdxCRepN cmax evs idx)
    {k : GoString} {X : KeyIndex} (hg : idxGet idx k = some X) :
    ∃ c : Int, -1 ≤ c ∧ c ≤ cmax ∧ ∃ gi j, CutLe (W64 c) (kiOfKey evs k) gi j ∧
      kiNorm X = kiNorm (kiCutAt gi j (kiOfKey evs k)) ∧ kiIsEmpty (kiCutAt gi j (kiOfKey evs k)) = false := by
  obtain ⟨c, h0, h1, gi, j, hc, he⟩ := h.2 k
  refine ⟨c, h0, h1, gi, j, hc, ?_⟩
  rw [hg] at he
  unfold kiCutO at he
  split at he
  · cases he
  · rename_i hne
    simp only [Option.map_some, Option.some.injEq] at he
    exact ⟨he, by simpa using hne⟩

/-- A key the index does not have: its cut is empty. -/
theorem IdxCRepN.get_none {cmax : Int} {evs : List Ev} {idx : IndexM} (h : IdxCRepN cmax evs idx)
    {k : GoString} (hg : idxGet idx k = none) :
    ∃ c : Int, -1 ≤ c ∧ c ≤ cmax ∧ ∃ gi j, CutLe (W64 c) (kiOfKey evs k) gi j ∧
      kiIsEmpty (kiCutAt gi j (kiOfKey evs k)) = true := by
  obtain ⟨c, h0, h1, gi, j, hc, he⟩ := h.2 k
  refine ⟨c, h0, h1, gi, j, hc, ?_⟩
  rw [hg] at he
  unfold kiCutO at he
  split at he
  · assumption
  · cases he

/-- The cut's generations are as `doCompact` walks them. -/
theorem kiCutAt_gensOk {ki : KeyIndex} (hwf : KiWf ki) {gi j : Nat} (hp : CutPos ki gi j) :
    (kiCutAt gi j ki).gens ≠ [] ∧
      ∀ i, i + 1 < (kiCutAt gi j ki).gens.length → ((kiCutAt gi j ki).gens.getD i Gen.empty).revs ≠ [] := by
  have hlt := hp.1
  refine ⟨kiCutAt_gens_ne hp, fun i hi => ?_⟩
  rw [kiCutAt_gens, dropSet_length] at hi
  rw [kiCutAt_gens]
  cases i with
  | zero =>
    rw [dropSet_getD0 _ _ _ _ hlt]
    have hne := hwf.nonlast gi (by omega)
    rw [Ne, genDrop_revs_ne hp.2]; exact hne
  | succ t =>
    rw [dropSet_getDs]; exact hwf.nonlast _ (by omega)

/-- **What a key index of the tree shares with the log's**: not empty, the same last change and
emptiness of the last generation, generations as `doCompact` walks them. -/
theorem IdxCRepN.get_facts {cmax : Int} {evs : List Ev} {idx : IndexM} (h : IdxCRepN cmax evs idx)
    {k : GoString} {X : KeyIndex} (hg : idxGet idx k = some X) :
    kiIsEmpty X = false ∧ X.modified = (kiOfKey evs k).modified ∧
      kiLastEmpty X = kiLastEmpty (kiOfKey evs k) ∧
      (X.gens ≠ [] ∧ ∀ i, i + 1 < X.gens.length → (X.gens.getD i Gen.empty).revs ≠ []) := by
  obtain ⟨c, -, -, gi, j, hc, hn, hne⟩ := h.get_some hg
  have hwf := kiOfKey_wf evs k
  have hp := hc.cutPos hwf
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← kiIsEmpty_kiNorm, hn, kiIsEmpty_kiNorm]; exact hne
  · rw [← kiNorm_modified X, hn, kiNorm_modified, kiCutAt_modified]
  · rw [← kiLastEmpty_kiNorm X, hn, kiLastEmpty_kiNorm, kiLastEmpty_cutAt hp]
  · rw [← gensOk_kiNorm, hn, gensOk_kiNorm]; exact kiCutAt_gensOk hwf hp

/-- A key the index does not have: its last generation is empty (a tombstone finds nothing). -/
theorem IdxCRepN.lastEmpty_none {cmax : Int} {evs : List Ev} {idx : IndexM} (h : IdxCRepN cmax evs idx)
    {k : GoString} (hg : idxGet idx k = none) : kiLastEmpty (kiOfKey evs k) = true := by
  obtain ⟨c, -, -, gi, j, hc, he⟩ := h.get_none hg
  rw [← kiLastEmpty_cutAt (hc.cutPos (kiOfKey_wf evs k))]
  exact kiIsEmpty_lastEmpty he

/-- **The writer's next event** keeps the representation (its revision is above every level). -/
theorem IdxCRepN.step (ilog : Log) (pend : List Change) (x : Change)
    (hb : LogB (ilog ++ [pend ++ [x]])) {cmax : Int} {idx : IndexM} (hcmax : cmax < ilog.length)
    (h : IdxCRepN cmax (evsOf (ilog ++ [pend])) idx) :
    IdxCRepN cmax (evsOf (ilog ++ [pend ++ [x]]))
      (idxApply idx (evOfChange ilog.length pend.length x)) := by
  have hlen : ilog.length + 1 < 2 ^ 63 := by have := hb.1; simp at this; omega
  obtain ⟨hs, hk⟩ := h
  have hevs : evsOf (ilog ++ [pend ++ [x]]) = evsOf (ilog ++ [pend]) ++ [evOfChange ilog.length pend.length x] :=
    evsOf_append_change ilog pend x
  rw [hevs]
  have hrev : (evOfChange ilog.length pend.length x).rev.main = W64 ilog.length := rfl
  generalize evOfChange ilog.length pend.length x = ev at *
  refine ⟨idxApply_sorted hs ev, fun k => ?_⟩
  obtain ⟨c, h0, h1, gi, j, hc, he⟩ := hk k
  refine ⟨c, h0, h1, gi, j, ?_⟩
  rw [kiOfKey_append, idxGet_idxApply hs]
  by_cases hkk : ev.key = k
  · rw [ite_eq_left hkk, ite_eq_left hkk]
    have hwf := kiOfKey_wf (evsOf (ilog ++ [pend])) k
    have hcr : sint.Z (W64 c) < sint.Z ev.rev.main := by rw [hrev]; word
    refine ⟨hc.kiApply hwf ev hcr, ?_⟩
    rw [kiCutO_step hwf hc]
    exact stepO_norm ev he
  · rw [ite_eq_right hkk, ite_eq_right hkk]
    exact ⟨hc, he⟩

theorem sintZ_W64_of {c : Int} (h0 : -1 ≤ c) (h1 : c < 2 ^ 63) : sint.Z (W64 c) = c := by word

/-- A key index of the tree answers as the log's at or above every level. -/
theorem IdxCRepN.get_answer (log : Log) (hb : LogB log) {cmax : Int} {idx : IndexM}
    (h : IdxCRepN cmax (evsOf log) idx) (atRev : w64) (hc : cmax ≤ sint.Z atRev) (k : GoString) :
    kiGet ((idxGet idx k).getD kiEmpty) atRev = kiGet (kiOfKey (evsOf log) k) atRev := by
  have hs := kiOfKey_KiS log hb k
  have ha : sint.Z atRev < 2 ^ 63 := by word
  obtain ⟨c, h0, h1, gi, j, hc', he⟩ := h.2 k
  have hca : sint.Z (W64 c) ≤ sint.Z atRev := by rw [sintZ_W64_of h0 (by omega)]; omega
  rw [← kiGet_cutAt hs hca hc']
  cases hg : idxGet idx k with
  | none =>
    rw [hg] at he
    unfold kiCutO at he
    split at he
    · rename_i hE
      rw [Option.getD_none, kiGet_kiEmpty, kiGet_isEmpty hE]
    · cases he
  | some X =>
    rw [hg] at he
    unfold kiCutO at he
    split at he
    · cases he
    · simp only [Option.map_some, Option.some.injEq] at he
      rw [Option.getD_some, ← kiGet_kiNorm X, he, kiGet_kiNorm]

/-- **A reader at or above every level** reads the uncompacted index's answer. -/
theorem IdxCRepN.kiAt (log : Log) (hb : LogB log) {cmax : Int} {idx : IndexM}
    (h : IdxCRepN cmax (evsOf log) idx) (atRev : w64) (hc : cmax ≤ sint.Z atRev) (k : GoString) :
    kiGet (kiAt idx k) atRev = kiGet (kiOfKey (evsOf log) k) atRev :=
  h.get_answer log hb atRev hc k

/-- The empty key index's only cut is itself, empty. -/
theorem kiCutO_kiEmpty {c : w64} {gi j : Nat} (h : CutLe c kiEmpty gi j) : kiCutO gi j kiEmpty = none := by
  obtain ⟨-, hlt, hj⟩ := h.pos KiWf.kiEmpty
  have hgi : gi = 0 := by simp [kiEmpty] at hlt; omega
  subst hgi
  have hj0 : j = 0 := by
    rcases hj with hj | ⟨-, hj⟩
    · simp [kiEmpty, Gen.empty] at hj
    · exact hj
  subst hj0
  rfl

/-- **A range read at or above every level** reads the uncompacted index's answers (a key the
compaction or the cut removed has none there). -/
theorem IdxCRepN.rangeAt (log : Log) (hb : LogB log) {cmax : Int} {idx : IndexM}
    (h : IdxCRepN cmax (evsOf log) idx) (atRev : w64) (hc : cmax ≤ sint.Z atRev) (k e : GoString) :
    rangeAt idx k e atRev = rangeAt (indexOf (evsOf log)) k e atRev := by
  rw [rangeAt_eq_keys _ h.1, rangeAt_eq_keys _ (indexOf_sorted _)]
  have hans : ∀ key, kiGet (mvcc.kiAt idx key) atRev = kiGet (mvcc.kiAt (indexOf (evsOf log)) key) atRev := by
    intro key; rw [kiAt_indexOf]; exact h.kiAt log hb atRev hc key
  simp only [hans]
  have habsent : ∀ key, idxGet idx key = none → kiGet (kiOfKey (evsOf log) key) atRev = none := by
    intro key hg
    have := h.get_answer log hb atRev hc key
    rw [hg, Option.getD_none, kiGet_kiEmpty] at this
    exact this.symm
  have hsortI : (idx.map Prod.fst).Pairwise go.GoStringLt := by rw [List.pairwise_map]; exact h.1
  have hsub : ((idx.map Prod.fst).filter (inRange k e)).Sublist
      (((indexOf (evsOf log)).map Prod.fst).filter (inRange k e)) := by
    apply List.Sublist.filter
    apply sublist_of_subset_sorted _ _ hsortI (keys_sorted _)
    intro x hx
    rw [mem_keys_iff]
    rw [List.mem_map] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    have hg := idxGet_of_mem idx h.1 z hz
    obtain ⟨c, -, -, gi, j, hc', he⟩ := h.2 z.1
    rw [hg] at he
    intro hE
    rw [hE] at hc' he
    rw [kiCutO_kiEmpty hc'] at he
    cases he
  symm
  apply filterMap_sublist_eq _ hsub (nodup_of_sorted ((keys_sorted _).filter _))
  intro x hx hnx
  rw [List.mem_filter] at hx
  have hx0 : x ∉ idx.map Prod.fst := fun h' => hnx (List.mem_filter.2 ⟨h', hx.2⟩)
  have hg : idxGet idx x = none := by
    cases hg : idxGet idx x with
    | none => rfl
    | some ki => exact absurd (List.mem_map.2 ⟨(x, ki), idxGet_some_mem h.1 hg, rfl⟩) hx0
  rw [kiAt_indexOf, habsent x hg]
  rfl

/-- A key the index has: its generations as `doCompact` walks them. -/
theorem IdxCRepN.gensOk {cmax : Int} {evs : List Ev} {idx : IndexM} (h : IdxCRepN cmax evs idx)
    {k : GoString} {ki : KeyIndex} (hg : idxGet idx k = some ki) :
    ki.gens ≠ [] ∧ ∀ i, i + 1 < ki.gens.length → (ki.gens.getD i Gen.empty).revs ≠ [] :=
  (h.get_facts hg).2.2.2

/-- A key the index has: compaction at `c ≥ cmax` keeps of it what it keeps of the log's. -/
theorem IdxCRepN.avail_some {cmax : Int} {log : Log} (hb : LogB log) {idx : IndexM}
    (h : IdxCRepN cmax (evsOf log) idx) (c : Int) (hc : cmax ≤ c) (hc' : c < 2 ^ 63)
    {k : GoString} {ki : KeyIndex} (hg : idxGet idx k = some ki) :
    kiAvail (W64 c) ki = kiAvail (W64 c) (kiOfKey (evsOf log) k) := by
  obtain ⟨c0, h0, h1, gi, j, hcut, hn, -⟩ := h.get_some hg
  rw [← kiAvail_kiNorm, hn, kiAvail_kiNorm]
  exact kiAvail_cutAt (kiOfKey_wf _ k) (by rw [sintZ_W64_of h0 (by omega), sintZ_W64_of (by omega) hc']; omega) hcut

/-- A key the index does not have: compaction at `c ≥ cmax` keeps nothing of it. -/
theorem IdxCRepN.avail_none {cmax : Int} {log : Log} (hb : LogB log) {idx : IndexM}
    (h : IdxCRepN cmax (evsOf log) idx) (c : Int) (hc : cmax ≤ c) (hc' : c < 2 ^ 63)
    {k : GoString} (hg : idxGet idx k = none) :
    kiAvail (W64 c) (kiOfKey (evsOf log) k) = none := by
  obtain ⟨c0, h0, h1, gi, j, hcut, he⟩ := h.get_none hg
  rw [← kiAvail_cutAt (kiOfKey_wf _ k) (by rw [sintZ_W64_of h0 (by omega), sintZ_W64_of (by omega) hc']; omega) hcut]
  exact kiAvail_isEmpty he _

/-- A key the index has: `keep` at `rev ≥ cmax` keeps of it what it keeps of the log's. -/
theorem IdxCRepN.keep_some {cmax : Int} {log : Log} (hb : LogB log) {idx : IndexM}
    (h : IdxCRepN cmax (evsOf log) idx) (rev : w64) (hc : cmax ≤ sint.Z rev)
    {k : GoString} {ki : KeyIndex} (hg : idxGet idx k = some ki) :
    kiKeep rev ki = kiKeep rev (kiOfKey (evsOf log) k) := by
  obtain ⟨c0, h0, h1, gi, j, hcut, hn, -⟩ := h.get_some hg
  have : sint.Z rev < 2 ^ 63 := by word
  rw [← kiKeep_kiNorm, hn, kiKeep_kiNorm]
  exact kiKeep_cutAt (kiOfKey_wf _ k) (by rw [sintZ_W64_of h0 (by omega)]; omega) hcut

/-- A key the index does not have: `keep` at `rev ≥ cmax` keeps nothing of it. -/
theorem IdxCRepN.keep_none {cmax : Int} {log : Log} (hb : LogB log) {idx : IndexM}
    (h : IdxCRepN cmax (evsOf log) idx) (rev : w64) (hc : cmax ≤ sint.Z rev)
    {k : GoString} (hg : idxGet idx k = none) :
    kiKeep rev (kiOfKey (evsOf log) k) = none := by
  obtain ⟨c0, h0, h1, gi, j, hcut, he⟩ := h.get_none hg
  have : sint.Z rev < 2 ^ 63 := by word
  rw [← kiKeep_cutAt (kiOfKey_wf _ k) (by rw [sintZ_W64_of h0 (by omega)]; omega) hcut]
  unfold kiKeep
  rw [he]; rfl

/-- The cut drops revisions, adds none. -/
theorem kiRevs_cutAt {gi j : Nat} {ki : KeyIndex} {r : Rev} (h : r ∈ kiRevs (kiCutAt gi j ki)) :
    r ∈ kiRevs ki := by
  unfold kiRevs at h
  rw [List.mem_flatten] at h
  obtain ⟨rs, hrs, hr⟩ := h
  rw [List.mem_map] at hrs
  obtain ⟨g', hg', rfl⟩ := hrs
  rw [kiCutAt_gens] at hg'
  have hg'' := List.mem_of_mem_drop hg'
  rcases List.mem_or_eq_of_mem_set hg'' with hm | he
  · exact kiRevs_mem hm hr
  · subst he
    generalize hg : ki.gens.getD gi Gen.empty = g at *
    have hr' : r ∈ g.revs := List.mem_of_mem_drop hr
    rw [List.getD_eq_getElem?_getD] at hg
    cases hx : ki.gens[gi]? with
    | none =>
      rw [hx] at hg; simp only [Option.getD_none] at hg; subst hg
      simp [Gen.empty] at hr'
    | some x =>
      rw [hx] at hg; simp only [Option.getD_some] at hg; subst hg
      exact kiRevs_mem (List.mem_of_getElem? hx) hr'

/-- **Two keys' kept revisions differ** (a revision is one event's, of one key). -/
theorem IdxCRepN.avail_inj {cmax : Int} {log : Log} (hb : LogB log) {idx : IndexM}
    (h : IdxCRepN cmax (evsOf log) idx) {k1 k2 : GoString} {ki1 ki2 : KeyIndex} {c : w64} {r : Rev}
    (h1 : idxGet idx k1 = some ki1) (h2 : idxGet idx k2 = some ki2)
    (hr1 : kiAvail c ki1 = some r) (hr2 : kiAvail c ki2 = some r) : k1 = k2 := by
  have hmem : ∀ {k : GoString} {X : KeyIndex}, idxGet idx k = some X → kiAvail c X = some r →
      r ∈ kiRevs (kiOfKey (evsOf log) k) := by
    intro k X hg hr
    obtain ⟨-, -, -, gi, j, -, hn, -⟩ := h.get_some hg
    have := kiAvail_mem hr
    rw [← kiRevs_kiNorm, hn, kiRevs_kiNorm] at this
    exact kiRevs_cutAt this
  obtain ⟨e1, he1, hr1', hk1⟩ := kiRevs_kiOfKey (hmem h1 hr1)
  obtain ⟨e2, he2, hr2', hk2⟩ := kiRevs_kiOfKey (hmem h2 hr2)
  have := evsOf_rev_inj log hb he1 he2 (hr1'.trans hr2'.symm)
  subst this
  rw [← hk1, ← hk2]

/-- **A compaction step** (`treeIndex.Compact`'s, under the lock): the key at `i` compacted at
`c' ≥ cmax`, deleted if that empties it; every key's level is then at most `c'`. -/
theorem IdxCRepN.compactAt {cmax c' : Int} {log : Log} (hb : LogB log) {idx : IndexM}
    (h : IdxCRepN cmax (evsOf log) idx) (hle : cmax ≤ c') (hc' : c' < 2 ^ 63)
    (i : Nat) (k : GoString) (ki : KeyIndex) (hi : idx[i]? = some (k, ki)) :
    IdxCRepN c' (evsOf log)
      (if kiIsEmpty (kiCompact (W64 c') ki) then idx.eraseIdx i else idx.set i (k, kiCompact (W64 c') ki)) := by
  have hs := h.1
  have hmem : (k, ki) ∈ idx := List.mem_of_getElem? hi
  have hk : idxGet idx k = some ki := idxGet_of_mem idx hs _ hmem
  obtain ⟨c0, h0, h1, gi, j, hcut, hn, -⟩ := h.get_some hk
  have hcc : kiNorm (kiCompact (W64 c') ki) = kiNorm (kiCompact (W64 c') (kiOfKey (evsOf log) k)) := by
    rw [← kiNorm_kiCompact, hn, kiNorm_kiCompact,
      kiCompact_cutAt (kiOfKey_wf _ k) (by rw [sintZ_W64_of h0 (by omega), sintZ_W64_of (by omega) hc']; omega) hcut]
  have hce : kiIsEmpty (kiCompact (W64 c') ki) = kiIsEmpty (kiCompact (W64 c') (kiOfKey (evsOf log) k)) := by
    rw [← kiIsEmpty_kiNorm, hcc, kiIsEmpty_kiNorm]
  have hnew : ∀ o : Option KeyIndex, o.map kiNorm = (kiCompactO c' (kiOfKey (evsOf log) k)).map kiNorm →
      ∃ c : Int, -1 ≤ c ∧ c ≤ c' ∧ ∃ gi j, CutLe (W64 c) (kiOfKey (evsOf log) k) gi j ∧
        o.map kiNorm = (kiCutO gi j (kiOfKey (evsOf log) k)).map kiNorm := by
    intro o ho
    exact ⟨c', by omega, Int.le_refl _, _, _, CutLe.cmp _ _, by rw [ho, kiCompactO_eq_cutO]⟩
  -- the other keys
  have hother : ∀ (idx' : IndexM), idx'.Pairwise idxLess →
      (∀ k', k' ≠ k → ∀ v, (k', v) ∈ idx' ↔ (k', v) ∈ idx) →
      ∀ k', k' ≠ k → ∃ c : Int, -1 ≤ c ∧ c ≤ c' ∧ ∃ gi j, CutLe (W64 c) (kiOfKey (evsOf log) k') gi j ∧
        (idxGet idx' k').map kiNorm = (kiCutO gi j (kiOfKey (evsOf log) k')).map kiNorm := by
    intro idx' hs' hm k' hk'
    obtain ⟨c1, h10, h11, h12⟩ := h.2 k'
    exact ⟨c1, h10, by omega, by rw [idxGet_congr hs hs' (hm k' hk')]; exact h12⟩
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
      apply hnew
      unfold kiCompactO
      rw [← hce, ite_eq_left he]
      rw [idxGet_none_of_not_mem hs' (by
        intro v hv
        rw [List.mem_eraseIdx_iff_getElem?] at hv
        obtain ⟨j, hji, hj⟩ := hv
        exact hji (idx_key_unique hs hj hi rfl))]
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
      apply hnew
      unfold kiCompactO
      rw [← hce, ite_eq_right he]
      rw [idxGet_of_mem _ hs' (k', kiCompact (W64 c') ki) (by
        apply List.mem_of_getElem? (i := i)
        rw [List.getElem?_set_self hlt])]
      simp only [Option.map_some, hcc]
    · exact hother _ hs' hm k' hk'
