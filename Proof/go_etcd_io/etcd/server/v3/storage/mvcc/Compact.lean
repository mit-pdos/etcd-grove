/-
Compaction, the pure model (`key_index.go`'s `compact`/`keep`/`doCompact`, `index.go`'s
`Compact`/`Keep`): a key index compacted at a revision `c`, what it still answers, and the
revisions compaction keeps in the bucket. Lean-first; `notes/decisions.md`, "mvcc: compaction".

**The key index** (`kiCompact c ki`, mirroring `keyIndex.compact`): `doCompact` walks the
generations from the oldest while the generation is not the last and its tombstone's main is
below `c` (`compactGenIdx`), then, in that generation, finds the last revision with main at or
below `c` (`genWalk … (pAbove c)`, the walk `get` uses): the revision is *available* (kept in the
bucket, `kiAvail`), the generation is cut to start at it, and the earlier generations are
dropped. `keep` (the hash's) makes the same choice but does not keep a tombstone that ends a
generation that is not the last (`kiKeep`; the asymmetry the code documents).

**What a compacted key index answers** (`kiGet_kiCompact`): at every revision at or above `c`,
what the uncompacted one does; a compaction that empties it (`treeIndex.Compact` then deletes
the key) leaves nothing to answer there (`kiGet_of_kiCompact_empty`). Compactions compose
(`kiCompact_kiCompact`, `kiCompact_kiCompact_le`), compaction at `-1` changes nothing
(`kiCompact_neg`), and compaction commutes with the writer's next event, which is above `c`
(`kiCompactO_step`).

**The index** (`IdxCRep cmax evs idx`): the tree holds, for every key, its key index of the
events compacted at a level of its own (`-1 ≤ c ≤ cmax`: the job compacts key by key, under the
index lock each time), or nothing if that compaction emptied it. At revisions at or above `cmax`
the index answers what the uncompacted index does (`IdxCRep.kiAt`, `IdxCRep.rangeAt`).

**The bucket** (`KeyDel log c key`): the bucket keys compaction at `c` may delete: a revision
with main at or below `c` that compaction does not keep. A read at or above `c` never names one
(`named_not_del`), provided revision `c` does not delete a key and put it again
(`NoDelPutAt`): when it does, `doCompact` keeps the tombstone and drops the put that follows it
in the same revision, the key's live revision (`issues/etcd-compaction-delete-then-put.md`); the
premise is asserted by the one who compacts (`store.Compact`'s, since unit 6a) and carried by the
keys compaction deletes, so the compacted store's readers have it (`rangeAnswers_not_del`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Hist
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.BucketLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc

/-! ### Bounds -/

/-- A log the store can have: fewer than `2 ^ 63` revisions, each of fewer than `2 ^ 63`
changes (the index's history and the writer's budget keep it so). -/
def LogB (log : Log) : Prop := log.length < 2 ^ 63 ∧ ∀ cs ∈ log, cs.length < 2 ^ 63

/-- A compaction revision (`-1`: none) as a natural number, for the monotone counter. -/
def crevN (c : Int) : Nat := (c + 1).toNat

theorem crevN_le {c c' : Int} (h0 : -1 ≤ c) (h0' : -1 ≤ c') (h : crevN c ≤ crevN c') : c ≤ c' := by
  unfold crevN at h; omega

theorem crevN_mono {c c' : Int} (h : c ≤ c') : crevN c ≤ crevN c' := by
  unfold crevN; omega

theorem crevN_neg : crevN (-1) = 0 := rfl

/-! ### The key index (`key_index.go`) -/

/-- `doCompact`'s generation: from the oldest, the first that is the last one or whose
tombstone (last revision) has a main at or above `atRev`. -/
def compactGenIdx (atRev : w64) : List Gen → Nat
  | [] => 0
  | [_] => 0
  | g :: g' :: gs =>
    if sint.Z (g.revs.getLastD Rev.zero).main < sint.Z atRev then compactGenIdx atRev (g' :: gs) + 1
    else 0

/-- `doCompact`'s revision index in its generation: the last revision with main at or below
`atRev` (`walk` with `get`'s predicate), `-1` if none. -/
def compactRevIdx (atRev : w64) (ki : KeyIndex) : Int :=
  genWalk (ki.gens.getD (compactGenIdx atRev ki.gens) Gen.empty).revs (pAbove atRev)

/-- `keyIndex.compact(atRev)`: the generation `doCompact` found cut to start at its revision
(if it has one), the earlier generations dropped. `modified` is unchanged. -/
def kiCompact (atRev : w64) (ki : KeyIndex) : KeyIndex :=
  let gi := compactGenIdx atRev ki.gens
  let g := ki.gens.getD gi Gen.empty
  let ri := genWalk g.revs (pAbove atRev)
  let g' : Gen := if g.revs ≠ [] ∧ ri ≠ -1 then { g with revs := g.revs.drop ri.toNat } else g
  { ki with gens := (ki.gens.set gi g').drop gi }

/-- The revision `doCompact` adds to `available`: compaction keeps it in the bucket. -/
def kiAvail (atRev : w64) (ki : KeyIndex) : Option Rev :=
  let g := ki.gens.getD (compactGenIdx atRev ki.gens) Gen.empty
  let ri := genWalk g.revs (pAbove atRev)
  if ri = -1 then none else some (g.revs.getD ri.toNat Rev.zero)

/-- The revision `keep` leaves in `available` (the hash's `treeIndex.Keep`): `doCompact`'s, but
not a tombstone that ends a generation that is not the last; nothing for an empty key index. -/
def kiKeep (atRev : w64) (ki : KeyIndex) : Option Rev :=
  if kiIsEmpty ki then none
  else
    let gi := compactGenIdx atRev ki.gens
    let g := ki.gens.getD gi Gen.empty
    let ri := genWalk g.revs (pAbove atRev)
    if ri = -1 then none
    else if g.revs ≠ [] ∧ ri = ((g.revs.length - 1 : Nat) : Int) ∧ gi ≠ ki.gens.length - 1 then none
    else some (g.revs.getD ri.toNat Rev.zero)

/-- A key index compacted at `c` (`-1`: not compacted), or nothing if the compaction emptied it
(`treeIndex.Compact` deletes it from the tree; an absent key's index, `kiEmpty`, stays absent). -/
def kiCompactO (c : Int) (ki : KeyIndex) : Option KeyIndex :=
  if kiIsEmpty (kiCompact (W64 c) ki) then none else some (kiCompact (W64 c) ki)

theorem kiCompact_modified (c : w64) (ki : KeyIndex) : (kiCompact c ki).modified = ki.modified := rfl

/-! ### Proof helpers: the structure of a log's key index, the scan, the walk, the cut -/

/-! ### Helpers -/

/-- The main of a generation's last revision (its tombstone, for one that is not the last). -/
def tombZ (g : Gen) : Int := sint.Z (g.revs.getLastD Rev.zero).main

theorem compactGenIdx_lt (atRev : w64) : ∀ (G : List Gen), G ≠ [] → compactGenIdx atRev G < G.length
  | [], h => absurd rfl h
  | [_], _ => by simp [compactGenIdx]
  | g :: g' :: gs, _ => by
    unfold compactGenIdx
    split
    · have := compactGenIdx_lt atRev (g' :: gs) (by simp); simp at this ⊢; omega
    · simp

theorem compactGenIdx_before (atRev : w64) : ∀ (G : List Gen) (j : Nat), j < compactGenIdx atRev G →
    tombZ (G.getD j Gen.empty) < sint.Z atRev
  | [], j, h => by simp [compactGenIdx] at h
  | [_], j, h => by simp [compactGenIdx] at h
  | g :: g' :: gs, j, h => by
    unfold compactGenIdx at h
    split at h
    · rename_i hlt
      cases j with
      | zero => simp only [List.getD_cons_zero]; exact hlt
      | succ j =>
        have := compactGenIdx_before atRev (g' :: gs) j (by omega)
        simp only [List.getD_cons_succ]; exact this
    · simp at h

theorem compactGenIdx_stop (atRev : w64) : ∀ (G : List Gen), G ≠ [] →
    compactGenIdx atRev G + 1 = G.length ∨ ¬ tombZ (G.getD (compactGenIdx atRev G) Gen.empty) < sint.Z atRev
  | [], h => absurd rfl h
  | [_], _ => by simp [compactGenIdx]
  | g :: g' :: gs, _ => by
    unfold compactGenIdx
    split
    · rcases compactGenIdx_stop atRev (g' :: gs) (by simp) with h | h
      · left; simp at h ⊢; omega
      · right; simp only [List.getD_cons_succ]; exact h
    · rename_i hlt; right; simp only [List.getD_cons_zero]; exact hlt

theorem compactGenIdx_eq (atRev : w64) : ∀ (G : List Gen) (gi : Nat), gi < G.length →
    (∀ j, j < gi → tombZ (G.getD j Gen.empty) < sint.Z atRev) →
    (gi + 1 = G.length ∨ ¬ tombZ (G.getD gi Gen.empty) < sint.Z atRev) →
    compactGenIdx atRev G = gi
  | [], gi, h, _, _ => by simp at h
  | [_], gi, h, _, _ => by simp at h; simp [compactGenIdx]; omega
  | g :: g' :: gs, gi, h, hb, hs => by
    unfold compactGenIdx
    cases gi with
    | zero =>
      rcases hs with hs | hs
      · simp at hs
      · simp only [List.getD_cons_zero] at hs; simp only [tombZ] at hs; simp only [hs, ↓reduceIte]
    | succ gi =>
      have h0 := hb 0 (by omega)
      simp only [List.getD_cons_zero, tombZ] at h0
      simp only [h0, ↓reduceIte, Nat.add_right_cancel_iff]
      apply compactGenIdx_eq atRev (g' :: gs) gi (by simp at h ⊢; omega)
      · intro j hj; have := hb (j + 1) (by omega); simp only [List.getD_cons_succ] at this; exact this
      · rcases hs with hs | hs
        · left; simp at hs ⊢; omega
        · right; simp only [List.getD_cons_succ] at hs; exact hs

/-- `genWalk`, characterized. -/
theorem genWalk_spec (revs : List Rev) (p : Rev → Bool) :
    (genWalk revs p = -1 ∧ ∀ r ∈ revs, p r = true) ∨
    ∃ (j : Nat) (hj : j < revs.length), genWalk revs p = j ∧ p revs[j] = false ∧
      ∀ (k : Nat) (hk : k < revs.length), j < k → p revs[k] = true := by
  cases hf : revs.reverse.findIdx? (fun r => !p r) with
  | none =>
    left
    have hall : ∀ r ∈ revs, p r = true := by
      intro r hr
      have := List.findIdx?_eq_none_iff.1 hf r (List.mem_reverse.2 hr)
      simpa using this
    exact ⟨genWalk_eq_none hall, hall⟩
  | some i =>
    right
    obtain ⟨hi, hpi, hmin⟩ := List.findIdx?_eq_some_iff_getElem.1 hf
    rw [List.length_reverse] at hi
    refine ⟨revs.length - 1 - i, by omega, ?_, ?_, ?_⟩
    · unfold genWalk; rw [hf]
    · rw [List.getElem_reverse] at hpi; simpa using hpi
    · intro k hk hjk
      have := hmin (revs.length - 1 - k) (by omega)
      rw [List.getElem_reverse] at this
      have e : revs.length - 1 - (revs.length - 1 - k) = k := by omega
      simp only [e] at this
      simpa using this

theorem LogB.prefix {log : Log} {cs : List Change} (h : LogB (log ++ [cs])) : LogB log :=
  ⟨by have := h.1; simp at this; omega, fun c hc => h.2 c (List.mem_append_left _ hc)⟩

theorem LogB.prefix' {log log' : Log} (h : LogB log') (hpre : log <+: log') : LogB log :=
  ⟨by have := hpre.length_le; have := h.1; omega, fun c hc => h.2 c (hpre.subset hc)⟩

/-! ### The events of a log: strictly increasing revisions -/

theorem snoc_induction {α : Type} {P : List α → Prop} (h0 : P [])
    (hs : ∀ l a, P l → P (l ++ [a])) : ∀ l, P l := by
  intro l
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact h0
  | cons a t ih => rw [List.reverse_cons]; exact hs _ a ih

theorem evsOfRev_mem (m : Nat) (cs : List Change) (e : Ev) (he : e ∈ evsOfRev m cs) :
    ∃ i, i < cs.length ∧ e.rev = ⟨W64 m, W64 i⟩ ∧ cs[i]? = some e.change := by
  unfold evsOfRev at he
  rw [List.mem_map] at he
  obtain ⟨p, hp, rfl⟩ := he
  obtain ⟨x, i⟩ := p
  rw [List.mem_zipIdx_iff_getElem?] at hp
  simp only at hp ⊢
  exact ⟨i, (List.getElem?_eq_some_iff.1 hp).1, rfl, hp⟩

/-- The events of a log: revisions strictly increasing, mains and subs in range, each the
change at its place in the log. -/
def EvOrd (log : Log) : Prop :=
  ((evsOf log).map Ev.rev).Pairwise Rev.lt ∧
    ∀ e ∈ evsOf log, 0 ≤ sint.Z e.rev.main ∧ sint.Z e.rev.main < log.length ∧
      0 ≤ sint.Z e.rev.sub ∧ ∃ cs, log[e.rev.main.toNat]? = some cs ∧ cs[e.rev.sub.toNat]? = some e.change

theorem evsOf_ord : ∀ (log : Log), LogB log → EvOrd log := by
  refine snoc_induction (P := fun log => LogB log → EvOrd log) ?_ ?_
  · intro _; simp [EvOrd, evsOf]
  intro log cs ih hb
  · 
    have hb' := hb.prefix
    obtain ⟨ih1, ih2⟩ := ih hb'
    unfold EvOrd
    have hlen : log.length + 1 < 2 ^ 63 := by have := hb.1; simp at this; omega
    have hcs : cs.length < 2 ^ 63 := hb.2 cs (by simp)
    rw [evsOf_append]
    refine ⟨?_, ?_⟩
    · rw [List.map_append, List.pairwise_append]
      refine ⟨ih1, ?_, ?_⟩
      · unfold evsOfRev
        rw [List.map_map, List.pairwise_map]
        rw [List.pairwise_iff_getElem]
        intro i j hi hj hij
        simp only [List.length_zipIdx] at hi hj
        simp only [List.getElem_zipIdx, Function.comp]
        right
        refine ⟨rfl, ?_⟩
        have : sint.Z (W64 ((0 + i : Nat) : Int)) = i := by word
        have : sint.Z (W64 ((0 + j : Nat) : Int)) = j := by word
        simp only [Nat.zero_add] at *
        omega
      · intro a ha b hb2
        rw [List.mem_map] at ha hb2
        obtain ⟨ea, hea, rfl⟩ := ha
        obtain ⟨eb, heb, rfl⟩ := hb2
        obtain ⟨i, hi, hr, -⟩ := evsOfRev_mem _ _ _ heb
        left
        rw [hr]
        have := (ih2 ea hea).2.1
        simp only
        have : sint.Z (W64 (log.length : Int)) = log.length := by word
        omega
    · intro e he
      rcases List.mem_append.1 he with he | he
      · obtain ⟨h1, h2, h3, cs', h4, h5⟩ := ih2 e he
        refine ⟨h1, by simp; omega, h3, cs', ?_, h5⟩
        have hl : e.rev.main.toNat < log.length := by word
        rw [List.getElem?_append_left hl]
        exact h4
      · obtain ⟨i, hi, hr, hc⟩ := evsOfRev_mem _ _ _ he
        rw [hr]
        simp only
        refine ⟨by word, by simp; word, by word, cs, ?_, ?_⟩
        · rw [show (W64 (log.length : Int)).toNat = log.length by word]; simp
        · rw [show (W64 (i : Int)).toNat = i by word]; exact hc

/-! ### The key index of a log's events: its structure -/

theorem kiRevs_kiApply {ki : KeyIndex} (hwf : KiWf ki) (e : Ev) :
    kiRevs (kiApply ki e) = kiRevs ki ∨ kiRevs (kiApply ki e) = kiRevs ki ++ [e.rev] := by
  unfold kiApply
  split
  · split
    · exact Or.inl rfl
    · exact Or.inr (kiRevs_kiTombstone hwf.ne _)
  · exact Or.inr (kiRevs_kiPut hwf.ne _)

theorem getElem?_dropLast_append {α : Type} (G : List α) (x : α) (h : G ≠ []) (i : Nat) :
    (G.dropLast ++ [x])[i]? =
      if i + 1 < G.length then G[i]? else if i + 1 = G.length then some x else none := by
  have hpos := List.length_pos_iff.2 h
  by_cases h1 : i + 1 < G.length
  · rw [ite_eq_left h1, List.getElem?_append_left (by rw [List.length_dropLast]; omega),
      List.getElem?_dropLast, ite_eq_left (by omega)]
  · rw [ite_eq_right h1, List.getElem?_append_right (by rw [List.length_dropLast]; omega),
      List.length_dropLast]
    by_cases h2 : i + 1 = G.length
    · rw [ite_eq_left h2, show i - (G.length - 1) = 0 by omega]; rfl
    · rw [ite_eq_right h2, List.getElem?_eq_none (by simp; omega)]

/-- Each revision of the key index is an event of `evs` of the key, a tombstone exactly when it
ends a generation that is not the last. -/
def KiEvs (evs : List Ev) (k : GoString) (ki : KeyIndex) : Prop :=
  ∀ (i p : Nat) (g : Gen) (r : Rev), ki.gens[i]? = some g → g.revs[p]? = some r →
    ∃ e ∈ evs, e.rev = r ∧ e.key = k ∧
      (e.tomb = true ↔ (i + 1 < ki.gens.length ∧ p + 1 = g.revs.length))

theorem KiEvs.mono {evs evs' : List Ev} {k : GoString} {ki : KeyIndex} (h : KiEvs evs k ki)
    (hsub : ∀ e ∈ evs, e ∈ evs') : KiEvs evs' k ki := by
  intro i p g r hg hr
  obtain ⟨e, he, h1⟩ := h i p g r hg hr
  exact ⟨e, hsub e he, h1⟩

theorem KiEvs.apply {evs : List Ev} {k : GoString} {ki : KeyIndex} (hwf : KiWf ki)
    (h : KiEvs evs k ki) (e : Ev) (hk : e.key = k) : KiEvs (evs ++ [e]) k (kiApply ki e) := by
  have hmono := h.mono (evs' := evs ++ [e]) (fun x hx => List.mem_append_left _ hx)
  have hne := hwf.ne
  have hpos := List.length_pos_iff.2 hne
  have hL : ki.gens[ki.gens.length - 1]? = some (ki.gens.getLastD Gen.empty) := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
    rw [List.getElem?_eq_getElem (by omega)]; rfl
  have he : e ∈ evs ++ [e] := List.mem_append_right _ (List.mem_singleton_self _)
  -- the put part, shared
  have hput : ∀ (T : Bool), e.tomb = T →
      ∀ (i p : Nat) (g : Gen) (r : Rev), (ki.gens.dropLast ++ [genPut (ki.gens.getLastD Gen.empty) e.rev])[i]? = some g →
        g.revs[p]? = some r →
        ∃ e' ∈ evs ++ [e], e'.rev = r ∧ e'.key = k ∧
          (e'.tomb = true ↔ ((T = true ∧ i + 1 = ki.gens.length ∧ p + 1 = g.revs.length) ∨
            (i + 1 < ki.gens.length ∧ p + 1 = g.revs.length))) := by
    intro T hT i p g r hg hr
    rw [getElem?_dropLast_append _ _ hne] at hg
    split at hg
    · rename_i hi
      obtain ⟨e', he', h1, h2, h3⟩ := hmono i p g r hg hr
      refine ⟨e', he', h1, h2, ?_⟩
      rw [h3]
      constructor
      · intro hh; exact Or.inr hh
      · rintro (⟨-, hh, -⟩ | hh)
        · omega
        · exact hh
    · split at hg
      · rename_i hi1 hi2
        cases hg
        simp only [genPut_revs] at hr ⊢
        rw [List.getElem?_append] at hr
        split at hr
        · rename_i hp
          obtain ⟨e', he', h1, h2, h3⟩ := hmono i p _ r (by rw [show i = ki.gens.length - 1 by omega]; exact hL) hr
          refine ⟨e', he', h1, h2, ?_⟩
          rw [h3]
          simp only [List.length_append, List.length_singleton]
          constructor
          · intro hh; omega
          · rintro (⟨-, -, hh⟩ | ⟨hh, -⟩) <;> omega
        · rename_i hp
          have hp' : p = (ki.gens.getLastD Gen.empty).revs.length := by
            cases hq : p - (ki.gens.getLastD Gen.empty).revs.length with
            | zero => omega
            | succ q => rw [hq] at hr; simp at hr
          rw [hp', Nat.sub_self] at hr
          simp at hr
          subst hr
          refine ⟨e, he, rfl, hk, ?_⟩
          simp only [List.length_append, List.length_singleton]
          rw [hT]
          cases T
          · simp only [Bool.false_eq_true, false_and, false_or, false_iff, not_and]
            intro hh; omega
          · simp only [true_and, true_iff]
            left; omega
      · cases hg
  unfold kiApply
  split
  · rename_i ht
    split
    · exact hmono
    · intro i p g r hg hr
      rw [kiTombstone_gens, kiPut_gens_of_ne hne] at hg ⊢
      rw [List.getElem?_append] at hg
      simp only [List.length_append, List.length_singleton, length_dropLast_append _ _ hne] at hg ⊢
      split at hg
      · rename_i hi0
        obtain ⟨e', he', h1, h2, h3⟩ := hput true ht i p g r hg hr
        refine ⟨e', he', h1, h2, ?_⟩
        rw [h3]; simp only [true_and]

        constructor
        · rintro (⟨h4, h5⟩ | ⟨h4, h5⟩) <;> exact ⟨by omega, h5⟩
        · rintro ⟨h4, h5⟩
          by_cases h6 : i + 1 = ki.gens.length
          · exact Or.inl ⟨h6, h5⟩
          · exact Or.inr ⟨by omega, h5⟩
      · rename_i hi
        have : i - ki.gens.length = 0 := by
          cases hq : i - ki.gens.length with
          | zero => rfl
          | succ q => rw [hq] at hg; simp at hg
        rw [this] at hg
        simp at hg
        subst hg
        simp [Gen.empty] at hr
  · rename_i ht
    intro i p g r hg hr
    rw [kiPut_gens_of_ne hne] at hg ⊢
    rw [length_dropLast_append _ _ hne]
    obtain ⟨e', he', h1, h2, h3⟩ := hput false (by simpa using ht) i p g r hg hr
    refine ⟨e', he', h1, h2, ?_⟩
    rw [h3]; simp

/-- The structure of a key index built from strictly increasing events. -/
structure KiS (ki : KeyIndex) : Prop where
  wf : KiWf ki
  sorted : (kiRevs ki).Pairwise Rev.lt
  nonneg : ∀ r ∈ kiRevs ki, 0 ≤ sint.Z r.main

theorem kiOfKey_struct (k : GoString) : ∀ (evs : List Ev),
    KiWf (kiOfKey evs k) ∧ (kiRevs (kiOfKey evs k)).Sublist (evs.map Ev.rev) ∧ KiEvs evs k (kiOfKey evs k) := by
  refine snoc_induction ?_ ?_
  · refine ⟨KiWf.kiEmpty, by simp [kiOfKey, kiRevs, kiEmpty, Gen.empty], ?_⟩
    intro i p g r hg hr
    simp only [kiOfKey, List.filter_nil, List.foldl_nil, kiEmpty] at hg
    cases i with
    | zero => simp at hg; subst hg; simp [Gen.empty] at hr
    | succ i => simp at hg
  · intro evs e ⟨h1, h2, h3⟩
    rw [kiOfKey_append]
    split
    · rename_i hk
      refine ⟨kiApply_wf h1 e, ?_, h3.apply h1 e hk⟩
      rw [List.map_append]
      rcases kiRevs_kiApply h1 e with h | h <;> rw [h]
      · exact h2.trans (List.sublist_append_left _ _)
      · exact h2.append (List.Sublist.refl _)
    · refine ⟨h1, ?_, h3.mono (fun x hx => List.mem_append_left _ hx)⟩
      rw [List.map_append]
      exact h2.trans (List.sublist_append_left _ _)

theorem kiOfKey_KiS (log : Log) (hb : LogB log) (k : GoString) : KiS (kiOfKey (evsOf log) k) := by
  obtain ⟨h1, h2, -⟩ := kiOfKey_struct k (evsOf log)
  obtain ⟨o1, o2⟩ := evsOf_ord log hb
  refine ⟨h1, o1.sublist h2, ?_⟩
  intro r hr
  have := h2.subset hr
  rw [List.mem_map] at this
  obtain ⟨e, he, rfl⟩ := this
  exact (o2 e he).1

/-! ### Derived facts of the structure -/

theorem Rev.lt_main_le {a b : Rev} (h : Rev.lt a b) : sint.Z a.main ≤ sint.Z b.main := by
  rcases h with h | ⟨h, -⟩
  · omega
  · rw [h]; exact Int.le_refl _

theorem getD_lt {α : Type} {l : List α} {i : Nat} (d : α) (h : i < l.length) : l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

theorem KiS.gen_sorted {ki : KeyIndex} (hs : KiS ki) {i : Nat} (hi : i < ki.gens.length) :
    (ki.gens.getD i Gen.empty).revs.Pairwise Rev.lt := by
  have := (List.pairwise_flatten.1 hs.sorted).1
  apply this
  rw [List.mem_map]
  exact ⟨_, by rw [getD_lt _ hi]; exact List.getElem_mem hi, rfl⟩

theorem KiS.cross {ki : KeyIndex} (hs : KiS ki) {i j : Nat} (hij : i < j) (hj : j < ki.gens.length)
    {a b : Rev} (ha : a ∈ (ki.gens.getD i Gen.empty).revs) (hb : b ∈ (ki.gens.getD j Gen.empty).revs) :
    Rev.lt a b := by
  have h2 := (List.pairwise_flatten.1 hs.sorted).2
  rw [List.pairwise_map, List.pairwise_iff_getElem] at h2
  rw [getD_lt _ (by omega)] at ha
  rw [getD_lt _ hj] at hb
  exact h2 i j (by omega) hj hij a ha b hb

theorem KiS.mem_nonneg {ki : KeyIndex} (hs : KiS ki) {i : Nat} (hi : i < ki.gens.length) {r : Rev}
    (hr : r ∈ (ki.gens.getD i Gen.empty).revs) : 0 ≤ sint.Z r.main := by
  apply hs.nonneg
  apply kiRevs_mem _ hr
  rw [getD_lt _ hi]; exact List.getElem_mem hi

/-- Sorted revisions: an earlier one's main is at or below a later one's. -/
theorem sorted_main_le {revs : List Rev} (hs : revs.Pairwise Rev.lt) {i j : Nat} (hij : i ≤ j)
    (hj : j < revs.length) : sint.Z (revs[i]'(by omega)).main ≤ sint.Z (revs[j]'hj).main := by
  rcases Nat.lt_or_eq_of_le hij with h | h
  · exact Rev.lt_main_le (List.pairwise_iff_getElem.1 hs i j (by omega) hj h)
  · subst h; exact Int.le_refl _

/-! ### The walk -/

theorem genWalk_ge {revs : List Rev} {p : Rev → Bool} {j : Nat} (hj : j < revs.length)
    (hp : p revs[j] = false) : (j : Int) ≤ genWalk revs p := by
  rcases genWalk_spec revs p with ⟨-, hall⟩ | ⟨j', hj', hw, -, hafter⟩
  · rw [hall _ (List.getElem_mem hj)] at hp; cases hp
  · rw [hw]
    by_cases h : j ≤ j'
    · omega
    · rw [hafter j hj (by omega)] at hp; cases hp

theorem genWalk_lt (revs : List Rev) (p : Rev → Bool) : genWalk revs p < revs.length :=
  (genWalk_range revs p).2

theorem genWalk_drop {revs : List Rev} {p : Rev → Bool} {d : Nat} (hd : (d : Int) ≤ genWalk revs p) :
    genWalk (revs.drop d) p = genWalk revs p - d := by
  rcases genWalk_spec revs p with ⟨hw, -⟩ | ⟨j, hj, hw, hf, hafter⟩
  · omega
  · rw [hw] at hd ⊢
    have hdj : d ≤ j := by omega
    rw [show ((j : Int) - d) = ((j - d : Nat) : Int) by omega]
    refine genWalk_eq_some (j - d) (by rw [List.length_drop]; omega) ?_ ?_
    · simp only [List.getElem_drop]
      have e : d + (j - d) = j := by omega
      simp only [e]; exact hf
    · intro k hk hjk
      simp only [List.getElem_drop]
      simp only [List.length_drop] at hk
      exact hafter (d + k) (by omega) (by omega)

/-- The walk at `c`: the last revision at or below `c`, or `-1`. -/
theorem genWalk_pAbove_spec (revs : List Rev) (c : w64) :
    (genWalk revs (pAbove c) = -1 ∧ ∀ r ∈ revs, sint.Z c < sint.Z r.main) ∨
    ∃ (j : Nat) (hj : j < revs.length), genWalk revs (pAbove c) = j ∧
      sint.Z revs[j].main ≤ sint.Z c ∧
      ∀ (k : Nat) (hk : k < revs.length), j < k → sint.Z c < sint.Z revs[k].main := by
  rcases genWalk_spec revs (pAbove c) with ⟨h1, h2⟩ | ⟨j, hj, h1, h2, h3⟩
  · left; exact ⟨h1, fun r hr => by have := h2 r hr; simpa [pAbove] using this⟩
  · right
    refine ⟨j, hj, h1, by simpa [pAbove] using h2, fun k hk hjk => ?_⟩
    have := h3 k hk hjk; simpa [pAbove] using this

/-! ### Dropping a prefix after setting its last element -/

theorem dropSet_length {α : Type} (G : List α) (gi : Nat) (x : α) :
    ((G.set gi x).drop gi).length = G.length - gi := by simp

theorem dropSet_getD0 {α : Type} (G : List α) (gi : Nat) (x d : α) (h : gi < G.length) :
    ((G.set gi x).drop gi).getD 0 d = x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_set]; simp [h]

theorem dropSet_getDs {α : Type} (G : List α) (gi j : Nat) (x d : α) :
    ((G.set gi x).drop gi).getD (j + 1) d = G.getD (gi + j + 1) d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_set, List.getD_eq_getElem?_getD]
  rw [ite_eq_right (by omega), Nat.add_assoc]

/-! ### Compaction, piece by piece -/

/-- The generation `doCompact` cut. -/
def cutGen (c : w64) (g : Gen) : Gen :=
  if g.revs ≠ [] ∧ genWalk g.revs (pAbove c) ≠ -1 then
    { g with revs := g.revs.drop (genWalk g.revs (pAbove c)).toNat } else g

theorem kiCompact_gens (c : w64) (ki : KeyIndex) :
    (kiCompact c ki).gens =
      (ki.gens.set (compactGenIdx c ki.gens)
        (cutGen c (ki.gens.getD (compactGenIdx c ki.gens) Gen.empty))).drop (compactGenIdx c ki.gens) := rfl

theorem cutGen_ver (c : w64) (g : Gen) : (cutGen c g).ver = g.ver := by
  unfold cutGen; split <;> rfl

theorem cutGen_created (c : w64) (g : Gen) : (cutGen c g).created = g.created := by
  unfold cutGen; split <;> rfl

theorem cutGen_cases (c : w64) (g : Gen) :
    cutGen c g = g ∨ ∃ (j : Nat) (hj : j < g.revs.length), genWalk g.revs (pAbove c) = j ∧
      sint.Z g.revs[j].main ≤ sint.Z c ∧ (cutGen c g).revs = g.revs.drop j ∧
      (∀ (k : Nat) (hk : k < g.revs.length), j < k → sint.Z c < sint.Z g.revs[k].main) := by
  unfold cutGen
  split
  · rename_i h
    right
    rcases genWalk_pAbove_spec g.revs c with ⟨h1, -⟩ | ⟨j, hj, h1, h2, h3⟩
    · exact absurd h1 h.2
    · refine ⟨j, hj, h1, h2, by rw [h1]; rfl, h3⟩
  · left; rfl

theorem cutGen_revs_ne (c : w64) (g : Gen) : (cutGen c g).revs = [] ↔ g.revs = [] := by
  rcases cutGen_cases c g with h | ⟨j, hj, -, -, h, -⟩
  · rw [h]
  · rw [h]; constructor
    · intro h'; have := congrArg List.length h'; simp at this; omega
    · intro h'; rw [h'] at hj; simp at hj

theorem cutGen_last (c : w64) (g : Gen) :
    (cutGen c g).revs.getLastD Rev.zero = g.revs.getLastD Rev.zero := by
  rcases cutGen_cases c g with h | ⟨j, hj, -, -, h, -⟩
  · rw [h]
  · rw [h, List.getLastD_eq_getLast?, List.getLastD_eq_getLast?, List.getLast?_drop]
    rw [ite_eq_right (by omega)]

theorem cutGen_tombZ (c : w64) (g : Gen) : tombZ (cutGen c g) = tombZ g := by
  unfold tombZ; rw [cutGen_last]

/-- The cut generation answers as the generation, at or above `c`. -/
theorem genGet_cutGen (c a : w64) (hca : sint.Z c ≤ sint.Z a) (g : Gen) :
    genGet (cutGen c g) a = genGet g a := by
  rcases cutGen_cases c g with h | ⟨j, hj, hw, hm, hr, -⟩
  · rw [h]
  · have hwa : (j : Int) ≤ genWalk g.revs (pAbove a) :=
      genWalk_ge hj (by simp [pAbove]; omega)
    have hwlt := genWalk_lt g.revs (pAbove a)
    have hne : g.revs ≠ [] := by intro h; rw [h] at hj; simp at hj
    have hne' : (cutGen c g).revs ≠ [] := fun h => hne ((cutGen_revs_ne c g).1 h)
    unfold genGet
    rw [hr] at hne' ⊢
    rw [genWalk_drop hwa, cutGen_created, cutGen_ver]
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
    rw [e3]

theorem kiFindGenAux_zero (gens : List Gen) (r : w64) : kiFindGenAux gens r 0 = none := rfl

/-- Below the compacted generation, the scan finds nothing (their tombstones are below `c`). -/
theorem findAux_below_none {ki : KeyIndex} (hwf : KiWf ki) (c a : w64) (hca : sint.Z c ≤ sint.Z a) :
    kiFindGenAux ki.gens a (compactGenIdx c ki.gens) = none := by
  have hlt := compactGenIdx_lt c ki.gens hwf.ne
  cases h : compactGenIdx c ki.gens with
  | zero => rfl
  | succ m =>
    have hb := compactGenIdx_before c ki.gens m (by omega)
    apply kiFindGenAux_tomb
    · exact hwf.nonlast m (by omega)
    · omega
    · unfold tombZ at hb; omega

theorem headD_drop (l : List Rev) (j : Nat) (hj : j < l.length) : (l.drop j).headD Rev.zero = l[j] := by
  rw [List.headD_eq_head?_getD, List.head?_drop, List.getElem?_eq_getElem hj]; rfl

/-- The compacted scan is the scan, shifted. -/
theorem findAux_compact {ki : KeyIndex} (hs : KiS ki) (c a : w64) (hca : sint.Z c ≤ sint.Z a) :
    ∀ j, j < ki.gens.length - compactGenIdx c ki.gens →
      kiFindGenAux (kiCompact c ki).gens a (j + 1) =
        (kiFindGenAux ki.gens a (compactGenIdx c ki.gens + j + 1)).map (fun x => x - compactGenIdx c ki.gens) ∧
      ∀ x, kiFindGenAux ki.gens a (compactGenIdx c ki.gens + j + 1) = some x → compactGenIdx c ki.gens ≤ x := by
  have hwf := hs.wf
  have hlt := compactGenIdx_lt c ki.gens hwf.ne
  generalize hgi : compactGenIdx c ki.gens = gi at hlt
  have hG : (kiCompact c ki).gens = (ki.gens.set gi (cutGen c (ki.gens.getD gi Gen.empty))).drop gi := by
    rw [kiCompact_gens, hgi]
  have hlen : (kiCompact c ki).gens.length = ki.gens.length - gi := by rw [hG, dropSet_length]
  have hnone := findAux_below_none hwf c a hca
  rw [hgi] at hnone
  intro j
  induction j with
  | zero =>
    intro _
    rw [kiFindGenAux_succ, kiFindGenAux_succ]
    rw [show (kiCompact c ki).gens.getD 0 Gen.empty = cutGen c (ki.gens.getD gi Gen.empty) by
      rw [hG, dropSet_getD0 _ _ _ _ hlt]]
    rw [hlen]
    generalize hg : ki.gens.getD gi Gen.empty = g
    simp only []
    by_cases he : g.revs = []
    · have he' : (cutGen c g).revs = [] := (cutGen_revs_ne c g).2 he
      simp only [he, he', ↓reduceIte, hnone, Option.map_none, kiFindGenAux_zero]
      exact ⟨by trivial, fun x hx => by cases hx⟩
    · have he' : (cutGen c g).revs ≠ [] := fun h => he ((cutGen_revs_ne c g).1 h)
      simp only [he, he', ↓reduceIte, cutGen_last]
      have hiff : (0 ≠ ki.gens.length - gi - 1) ↔ (gi ≠ ki.gens.length - 1) := by omega
      by_cases ht : gi ≠ ki.gens.length - 1 ∧ sint.Z (g.revs.getLastD Rev.zero).main ≤ sint.Z a
      · have ht' : 0 ≠ ki.gens.length - gi - 1 ∧ sint.Z (g.revs.getLastD Rev.zero).main ≤ sint.Z a :=
          ⟨hiff.2 ht.1, ht.2⟩
        simp only [ht, ht', ne_eq]
        exact ⟨by trivial, fun x hx => by cases hx⟩
      · have ht' : ¬ (0 ≠ ki.gens.length - gi - 1 ∧ sint.Z (g.revs.getLastD Rev.zero).main ≤ sint.Z a) := by
          rw [hiff]; exact ht
        rw [ite_eq_right ht, ite_eq_right ht']
        rcases cutGen_cases c g with hcut | ⟨j, hj, -, hm, hr, -⟩
        · rw [hcut]
          split
          · simp
          · simp [hnone, kiFindGenAux_zero]
        · have hsort : g.revs.Pairwise Rev.lt := by rw [← hg]; exact hs.gen_sorted hlt
          have h0 : sint.Z (g.revs.headD Rev.zero).main ≤ sint.Z a := by
            have := sorted_main_le hsort (Nat.zero_le j) hj
            have hh := headD_drop g.revs 0 (by omega)
            rw [List.drop_zero] at hh
            rw [hh]; omega
          have h0' : sint.Z ((cutGen c g).revs.headD Rev.zero).main ≤ sint.Z a := by
            rw [hr, headD_drop _ _ hj]; omega
          simp only [h0, h0', ↓reduceIte, Option.map_some, Nat.sub_self]
          exact ⟨by trivial, fun x hx => by cases hx; exact Nat.le_refl _⟩
  | succ j ih =>
    intro hj
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [kiFindGenAux_succ (cg := j + 1), show gi + (j + 1) + 1 = (gi + j + 1) + 1 by omega,
      kiFindGenAux_succ (cg := gi + j + 1)]
    rw [show (kiCompact c ki).gens.getD (j + 1) Gen.empty = ki.gens.getD (gi + j + 1) Gen.empty by
      rw [hG, dropSet_getDs]]
    rw [hlen]
    have hiff : (j + 1 ≠ ki.gens.length - gi - 1) ↔ (gi + j + 1 ≠ ki.gens.length - 1) := by omega
    generalize ki.gens.getD (gi + j + 1) Gen.empty = g
    simp only []
    by_cases he : g.revs = []
    · simp only [he, ↓reduceIte]; exact ⟨ih1, ih2⟩
    · simp only [he, ↓reduceIte]
      by_cases ht : gi + j + 1 ≠ ki.gens.length - 1 ∧ sint.Z (g.revs.getLastD Rev.zero).main ≤ sint.Z a
      · have ht' : j + 1 ≠ ki.gens.length - gi - 1 ∧ sint.Z (g.revs.getLastD Rev.zero).main ≤ sint.Z a :=
          ⟨hiff.2 ht.1, ht.2⟩
        rw [ite_eq_left ht, ite_eq_left ht']
        exact ⟨by trivial, fun x hx => by cases hx⟩
      · have ht' : ¬ (j + 1 ≠ ki.gens.length - gi - 1 ∧ sint.Z (g.revs.getLastD Rev.zero).main ≤ sint.Z a) := by
          rw [hiff]; exact ht
        rw [ite_eq_right ht, ite_eq_right ht']
        split
        · simp only [Option.map_some, Option.some.injEq]
          refine ⟨by omega, fun x hx => by cases hx; omega⟩
        · exact ⟨ih1, ih2⟩

/-- **(a), for any key index of this structure.** -/
theorem kiGet_kiCompact_S {ki : KeyIndex} (hs : KiS ki) (c a : w64) (hca : sint.Z c ≤ sint.Z a) :
    kiGet (kiCompact c ki) a = kiGet ki a := by
  have hwf := hs.wf
  have hlt := compactGenIdx_lt c ki.gens hwf.ne
  have hlen : (kiCompact c ki).gens.length = ki.gens.length - compactGenIdx c ki.gens := by
    rw [kiCompact_gens, dropSet_length]
  rw [kiGet_eq, kiGet_eq]
  unfold kiFindGen
  rw [hlen]
  obtain ⟨h1, h2⟩ := findAux_compact hs c a hca (ki.gens.length - compactGenIdx c ki.gens - 1) (by omega)
  rw [show ki.gens.length - compactGenIdx c ki.gens - 1 + 1 = ki.gens.length - compactGenIdx c ki.gens by omega] at h1
  rw [show compactGenIdx c ki.gens + (ki.gens.length - compactGenIdx c ki.gens - 1) + 1 = ki.gens.length by omega] at h1 h2
  rw [h1]
  cases hx : kiFindGenAux ki.gens a ki.gens.length with
  | none => rfl
  | some x =>
    have hgx := h2 x hx
    simp only [Option.map_some, Option.bind_some]
    rcases Nat.lt_or_eq_of_le hgx with hgt | heq
    · rw [show x - compactGenIdx c ki.gens = (x - compactGenIdx c ki.gens - 1) + 1 by omega,
        kiCompact_gens, dropSet_getDs, show compactGenIdx c ki.gens + (x - compactGenIdx c ki.gens - 1) + 1 = x by omega]
    · subst heq
      rw [Nat.sub_self, kiCompact_gens, dropSet_getD0 _ _ _ _ hlt, genGet_cutGen c a hca]

/-! ### Consequences: (b), no compaction, composition, the last generation -/

theorem kiGet_isEmpty {ki : KeyIndex} (h : kiIsEmpty ki = true) (a : w64) : kiGet ki a = none := by
  unfold kiIsEmpty at h
  rw [kiGet_eq]
  unfold kiFindGen
  split at h
  · rename_i g hg
    rw [hg]
    simp only [decide_eq_true_eq] at h
    simp [kiFindGenAux, h]
  · cases h

theorem compactGenIdx_neg {ki : KeyIndex} (hs : KiS ki) : compactGenIdx (W64 (-1)) ki.gens = 0 := by
  have hpos := List.length_pos_iff.2 hs.wf.ne
  apply compactGenIdx_eq _ _ 0 hpos (fun j hj => absurd hj (Nat.not_lt_zero _))
  right
  unfold tombZ
  have hm1 : sint.Z (W64 (-1)) = -1 := by decide
  rw [hm1]
  by_cases he : (ki.gens.getD 0 Gen.empty).revs = []
  · rw [he]; simp [Rev.zero]
  · have := hs.mem_nonneg hpos (getLastD_mem _ Rev.zero he)
    omega

theorem cutGen_neg {ki : KeyIndex} (hs : KiS ki) {i : Nat} (hi : i < ki.gens.length) :
    cutGen (W64 (-1)) (ki.gens.getD i Gen.empty) = ki.gens.getD i Gen.empty := by
  unfold cutGen
  rw [ite_eq_right]
  rintro ⟨-, h⟩
  apply h
  apply genWalk_eq_none
  intro r hr
  have := hs.mem_nonneg hi hr
  have hm1 : sint.Z (W64 (-1)) = -1 := by decide
  simp only [pAbove, hm1, decide_eq_true_eq]; omega

theorem KeyIndex.ext' {a b : KeyIndex} (h1 : a.modified = b.modified) (h2 : a.gens = b.gens) : a = b := by
  cases a; cases b; simp only at h1 h2; subst h1; subst h2; rfl

theorem kiCompact_neg_S {ki : KeyIndex} (hs : KiS ki) : kiCompact (W64 (-1)) ki = ki := by
  have hpos := List.length_pos_iff.2 hs.wf.ne
  have hg := kiCompact_gens (W64 (-1)) ki
  rw [compactGenIdx_neg hs, cutGen_neg hs hpos, List.drop_zero] at hg
  have hset : ki.gens.set 0 (ki.gens.getD 0 Gen.empty) = ki.gens := by
    apply set_same
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpos]; rfl
  rw [hset] at hg
  exact KeyIndex.ext' rfl hg

/-- The compacted generations' compaction index, at a revision at or above. -/
theorem compactGenIdx_compact_ge {ki : KeyIndex} (hwf : KiWf ki) (c c' : w64)
    (hcc : sint.Z c ≤ sint.Z c') :
    compactGenIdx c ki.gens ≤ compactGenIdx c' ki.gens ∧
    compactGenIdx c' (kiCompact c ki).gens = compactGenIdx c' ki.gens - compactGenIdx c ki.gens := by
  have hne := hwf.ne
  have hlt := compactGenIdx_lt c ki.gens hne
  have hlt' := compactGenIdx_lt c' ki.gens hne
  have hge : compactGenIdx c ki.gens ≤ compactGenIdx c' ki.gens := by
    apply Nat.le_of_not_lt
    intro hcon
    rcases compactGenIdx_stop c' ki.gens hne with h | h
    · omega
    · exact h (by have := compactGenIdx_before c ki.gens (compactGenIdx c' ki.gens) (by omega); omega)
  refine ⟨hge, ?_⟩
  generalize hgi : compactGenIdx c ki.gens = gi at *
  generalize hm : compactGenIdx c' ki.gens = m at *
  have hG : (kiCompact c ki).gens = (ki.gens.set gi (cutGen c (ki.gens.getD gi Gen.empty))).drop gi := by
    rw [kiCompact_gens, hgi]
  rw [hG]
  apply compactGenIdx_eq
  · rw [dropSet_length]; omega
  · intro j hj
    cases j with
    | zero =>
      rw [dropSet_getD0 _ _ _ _ hlt, cutGen_tombZ]
      exact compactGenIdx_before c' ki.gens gi (by omega)
    | succ j =>
      rw [dropSet_getDs]
      exact compactGenIdx_before c' ki.gens (gi + j + 1) (by omega)
  · rcases compactGenIdx_stop c' ki.gens hne with h | h
    · left; rw [dropSet_length]; omega
    · right
      rw [hm] at h
      rcases Nat.lt_or_eq_of_le hge with hgt | heq
      · rw [show m - gi = (m - gi - 1) + 1 by omega, dropSet_getDs,
          show gi + (m - gi - 1) + 1 = m by omega]; exact h
      · subst heq; rw [Nat.sub_self, dropSet_getD0 _ _ _ _ hlt, cutGen_tombZ]; exact h

theorem cutGen_cutGen (c c' : w64) (hcc : sint.Z c ≤ sint.Z c') (g : Gen) :
    cutGen c' (cutGen c g) = cutGen c' g := by
  rcases cutGen_cases c g with h | ⟨j, hj, -, hm, hr, -⟩
  · rw [h]
  · have hw' : (j : Int) ≤ genWalk g.revs (pAbove c') := genWalk_ge hj (by simp [pAbove]; omega)
    have hwlt := genWalk_lt g.revs (pAbove c')
    have hne : g.revs ≠ [] := by intro h; rw [h] at hj; simp at hj
    have hne' : (cutGen c g).revs ≠ [] := fun h => hne ((cutGen_revs_ne c g).1 h)
    have hc : cutGen c g = { g with revs := g.revs.drop j } := by
      cases g; simp only at hr ⊢; rw [← hr]; unfold cutGen; split <;> rfl
    rw [hc]
    rw [hc] at hne'
    unfold cutGen
    simp only at hne' ⊢
    rw [genWalk_drop hw']
    rw [ite_eq_left ⟨hne', by omega⟩, ite_eq_left ⟨hne, by omega⟩]
    simp only [List.drop_drop]
    congr 2; omega

theorem cutGen_cutGen_le (c c' : w64) (hcc : sint.Z c' ≤ sint.Z c) (g : Gen) :
    cutGen c' (cutGen c g) = cutGen c g := by
  rcases genWalk_pAbove_spec g.revs c with ⟨h1, h2⟩ | ⟨j, hj, h1, h2, h3⟩
  · have hc : cutGen c g = g := by unfold cutGen; rw [ite_eq_right]; rintro ⟨-, h⟩; exact h h1
    rw [hc]
    unfold cutGen
    rw [ite_eq_right]
    rintro ⟨-, h⟩
    apply h
    apply genWalk_eq_none
    intro r hr; have := h2 r hr; simp [pAbove]; omega
  · have hne : g.revs ≠ [] := by intro h; rw [h] at hj; simp at hj
    have hc : cutGen c g = { g with revs := g.revs.drop j } := by
      unfold cutGen; rw [ite_eq_left ⟨hne, by omega⟩, h1]; rfl
    rw [hc]
    unfold cutGen
    split
    · rename_i hh
      simp only at hh ⊢
      have hw : genWalk (g.revs.drop j) (pAbove c') = 0 := by
        rcases genWalk_pAbove_spec (g.revs.drop j) c' with ⟨h4, -⟩ | ⟨k, hk, h4, h5, -⟩
        · exact absurd h4 hh.2
        · rw [h4]
          cases k with
          | zero => rfl
          | succ k =>
            exfalso
            simp only [List.getElem_drop, List.length_drop] at h5 hk
            have := h3 (j + (k + 1)) (by omega) (by omega)
            omega
      rw [hw]; rfl
    · rfl

theorem dropSet_dropSet {α : Type} (G : List α) (gi m : Nat) (x y : α) (h : gi < m) :
    (((G.set gi x).drop gi).set (m - gi) y).drop (m - gi) = (G.set m y).drop m := by
  apply List.ext_getElem?
  intro t
  simp only [List.getElem?_drop, List.getElem?_set, List.length_drop, List.length_set]
  grind

theorem dropSet_set0 {α : Type} (G : List α) (gi : Nat) (x y : α) (h : gi < G.length) :
    ((G.set gi x).drop gi).set 0 y = (G.set gi y).drop gi := by
  apply List.ext_getElem?
  intro t
  simp only [List.getElem?_drop, List.getElem?_set, List.length_drop, List.length_set]
  grind

/-- Compactions compose (any key index of this structure). -/
theorem kiCompact_kiCompact_S {ki : KeyIndex} (hwf : KiWf ki) (c c' : w64) (hcc : sint.Z c ≤ sint.Z c') :
    kiCompact c' (kiCompact c ki) = kiCompact c' ki := by
  obtain ⟨hge, hidx⟩ := compactGenIdx_compact_ge hwf c c' hcc
  have hlt := compactGenIdx_lt c ki.gens hwf.ne
  refine KeyIndex.ext' rfl ?_
  rw [kiCompact_gens c' (kiCompact c ki), hidx, kiCompact_gens c ki, kiCompact_gens c' ki]
  generalize compactGenIdx c ki.gens = gi at *
  generalize compactGenIdx c' ki.gens = m at *
  rcases Nat.lt_or_eq_of_le hge with hgt | heq
  · rw [show m - gi = (m - gi - 1) + 1 by omega, dropSet_getDs,
      show gi + (m - gi - 1) + 1 = m by omega, show m - gi - 1 + 1 = m - gi by omega]
    exact dropSet_dropSet _ _ _ _ _ hgt
  · subst heq
    rw [Nat.sub_self, dropSet_getD0 _ _ _ _ hlt, cutGen_cutGen c c' hcc, List.drop_zero,
      dropSet_set0 _ _ _ _ hlt]

theorem kiCompact_kiCompact_le_S {ki : KeyIndex} (hwf : KiWf ki) (c c' : w64) (hcc : sint.Z c' ≤ sint.Z c) :
    kiCompact c' (kiCompact c ki) = kiCompact c ki := by
  have hne := hwf.ne
  have hlt := compactGenIdx_lt c ki.gens hne
  have hG := kiCompact_gens c ki
  generalize hgi : compactGenIdx c ki.gens = gi at *
  have h0 : compactGenIdx c' (kiCompact c ki).gens = 0 := by
    apply compactGenIdx_eq
    · rw [hG, dropSet_length]; omega
    · intro j hj; omega
    · rcases compactGenIdx_stop c ki.gens hne with h | h
      · left; rw [hG, dropSet_length]; rw [hgi] at h; omega
      · right; rw [hgi] at h; rw [hG, dropSet_getD0 _ _ _ _ hlt, cutGen_tombZ]; omega
  refine KeyIndex.ext' rfl ?_
  rw [kiCompact_gens c' (kiCompact c ki), h0, List.drop_zero]
  apply set_same
  rw [hG, List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_set, ite_eq_left (by omega),
    ite_eq_left hlt, List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_set,
    ite_eq_left (by omega), ite_eq_left hlt]
  simp only [Option.getD_some]
  rw [cutGen_cutGen_le c c' hcc]

/-- The compacted generations' last one. -/
theorem kiCompact_getLastD {ki : KeyIndex} (hwf : KiWf ki) (c : w64) :
    (kiCompact c ki).gens.getLastD Gen.empty =
      if compactGenIdx c ki.gens + 1 = ki.gens.length then
        cutGen c (ki.gens.getD (compactGenIdx c ki.gens) Gen.empty)
      else ki.gens.getLastD Gen.empty := by
  have hne := hwf.ne
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

theorem kiCompact_lastEmpty_S {ki : KeyIndex} (hwf : KiWf ki) (c : w64) :
    kiLastEmpty (kiCompact c ki) = kiLastEmpty ki := by
  unfold kiLastEmpty
  rw [kiCompact_getLastD hwf c]
  split
  · rename_i h
    rw [getLastD_eq_getD _ _ hwf.ne, show ki.gens.length - 1 = compactGenIdx c ki.gens by omega]
    simp only [decide_eq_decide]
    exact cutGen_revs_ne c _
  · rfl

theorem kiIsEmpty_lastEmpty {ki : KeyIndex} (h : kiIsEmpty ki = true) : kiLastEmpty ki = true := by
  unfold kiIsEmpty at h; unfold kiLastEmpty
  split at h
  · rename_i g hg; rw [hg]; simpa using h
  · cases h

/-! ### Compaction and the writer's next event -/

theorem cutGen_genPut (c : w64) (g : Gen) (rev : Rev) (hc : sint.Z c < sint.Z rev.main) :
    cutGen c (genPut g rev) = genPut (cutGen c g) rev := by
  have hw : genWalk (g.revs ++ [rev]) (pAbove c) = genWalk g.revs (pAbove c) :=
    genWalk_append_true _ _ _ (by simp [pAbove]; omega)
  rcases genWalk_pAbove_spec g.revs c with ⟨h1, -⟩ | ⟨j, hj, h1, -, -⟩
  · have hcg : cutGen c g = g := by unfold cutGen; rw [ite_eq_right]; rintro ⟨-, h⟩; exact h h1
    rw [hcg]
    unfold cutGen
    rw [ite_eq_right]
    rintro ⟨-, h⟩
    rw [genPut_revs, hw] at h; exact h h1
  · have hne : g.revs ≠ [] := by intro h; rw [h] at hj; simp at hj
    have hcg : cutGen c g = { g with revs := g.revs.drop j } := by
      unfold cutGen; rw [ite_eq_left ⟨hne, by omega⟩, h1]; rfl
    rw [hcg]
    unfold cutGen
    rw [genPut_revs, hw, h1, ite_eq_left ⟨by simp, by omega⟩]
    simp only [Int.toNat_natCast]
    unfold genPut
    have hd : g.revs.drop j ≠ [] := by
      intro h; have := congrArg List.length h; simp at this; omega
    simp only [hne, hd, ↓reduceIte, List.drop_append_of_le_length (Nat.le_of_lt hj)]

theorem compactGenIdx_put {ki : KeyIndex} (hwf : KiWf ki) (c : w64) (rev : Rev) :
    compactGenIdx c (ki.gens.dropLast ++ [genPut (ki.gens.getLastD Gen.empty) rev]) =
      compactGenIdx c ki.gens := by
  have hne := hwf.ne
  have hlt := compactGenIdx_lt c ki.gens hne
  have hlen := length_dropLast_append ki.gens (genPut (ki.gens.getLastD Gen.empty) rev) hne
  apply compactGenIdx_eq
  · omega
  · intro j hj
    rw [getD_dropLast_append_lt _ _ _ _ (by omega)]
    exact compactGenIdx_before c ki.gens j hj
  · by_cases hl : compactGenIdx c ki.gens + 1 = ki.gens.length
    · left; omega
    · right
      rw [getD_dropLast_append_lt _ _ _ _ (by omega)]
      rcases compactGenIdx_stop c ki.gens hne with h | h
      · omega
      · exact h

theorem dropSet_dropLast_append {α : Type} (G : List α) (gi : Nat) (w y : α) (hgi : gi + 1 < G.length) :
    ((G.dropLast ++ [y]).set gi w).drop gi = ((G.set gi w).drop gi).dropLast ++ [y] := by
  apply List.ext_getElem?
  intro t
  simp only [List.getElem?_drop, List.getElem?_set, List.getElem?_append, List.length_dropLast,
    List.length_drop, List.length_set, List.getElem?_dropLast, List.getElem?_singleton]
  by_cases h0 : t = 0
  · subst h0; simp; grind
  · by_cases h1 : gi + t + 1 < G.length
    · simp [h0]; grind
    · by_cases h2 : gi + t + 1 = G.length
      · simp [h0]; grind
      · simp [h0]; grind

theorem kiCompact_kiPut {ki : KeyIndex} (hwf : KiWf ki) (c : w64) (rev : Rev)
    (hc : sint.Z c < sint.Z rev.main) : kiCompact c (kiPut ki rev) = kiPut (kiCompact c ki) rev := by
  have hne := hwf.ne
  have hlt := compactGenIdx_lt c ki.gens hne
  have hG := kiCompact_gens c ki
  have hne' : (kiCompact c ki).gens ≠ [] := by
    intro h; have := congrArg List.length h; rw [hG, dropSet_length] at this; simp at this; omega
  refine KeyIndex.ext' rfl ?_
  rw [kiCompact_gens c (kiPut ki rev), kiPut_gens_of_ne hne, compactGenIdx_put hwf, kiPut_gens_of_ne hne',
    kiCompact_getLastD hwf, hG]
  generalize hgi : compactGenIdx c ki.gens = gi at *
  split
  · rename_i hlast
    rw [show gi = ki.gens.length - 1 by omega, getD_dropLast_append_last _ _ _ hne,
      cutGen_genPut c _ rev hc, getLastD_eq_getD _ _ hne]
    apply List.ext_getElem?
    intro t
    simp only [List.getElem?_drop, List.getElem?_set, List.length_drop, List.length_set,
      getElem?_dropLast_append _ _ hne, List.getElem?_append, List.length_dropLast, List.length_append,
      List.length_singleton, List.getElem?_singleton]
    grind
  · rename_i hlast
    rw [getD_dropLast_append_lt _ _ _ _ (by omega)]
    exact dropSet_dropLast_append _ _ _ _ (by omega)

theorem kiCompact_appendEmpty {ki : KeyIndex} (hne : ki.gens ≠ []) (c : w64)
    (hlast : ¬ tombZ (ki.gens.getLastD Gen.empty) < sint.Z c) :
    kiCompact c { ki with gens := ki.gens ++ [Gen.empty] } =
      { kiCompact c ki with gens := (kiCompact c ki).gens ++ [Gen.empty] } := by
  have hlt := compactGenIdx_lt c ki.gens hne
  have hidx : compactGenIdx c (ki.gens ++ [Gen.empty]) = compactGenIdx c ki.gens := by
    apply compactGenIdx_eq
    · simp; omega
    · intro j hj
      rw [getD_append_lt _ _ _ _ (by omega)]
      exact compactGenIdx_before c ki.gens j hj
    · right
      rw [getD_append_lt _ _ _ _ hlt]
      rcases compactGenIdx_stop c ki.gens hne with h | h
      · rw [getLastD_eq_getD _ _ hne, show ki.gens.length - 1 = compactGenIdx c ki.gens by omega] at hlast
        exact hlast
      · exact h
  refine KeyIndex.ext' rfl ?_
  show (kiCompact c { ki with gens := ki.gens ++ [Gen.empty] }).gens = (kiCompact c ki).gens ++ [Gen.empty]
  rw [kiCompact_gens, kiCompact_gens]
  simp only
  rw [hidx, getD_append_lt _ _ _ _ hlt]
  generalize compactGenIdx c ki.gens = gi at *
  apply List.ext_getElem?
  intro t
  simp only [List.getElem?_drop, List.getElem?_set, List.length_drop, List.length_set,
    List.getElem?_append, List.length_append, List.length_singleton]
  grind

theorem kiCompact_kiTombstone {ki : KeyIndex} (hwf : KiWf ki) (c : w64) (rev : Rev)
    (hc : sint.Z c < sint.Z rev.main) :
    kiCompact c (kiTombstone ki rev) = kiTombstone (kiCompact c ki) rev := by
  have hne := hwf.ne
  have hput := hwf.put rev
  have h1 : kiTombstone ki rev = { kiPut ki rev with gens := (kiPut ki rev).gens ++ [Gen.empty] } := rfl
  have h2 : kiTombstone (kiCompact c ki) rev =
      { kiPut (kiCompact c ki) rev with gens := (kiPut (kiCompact c ki) rev).gens ++ [Gen.empty] } := rfl
  rw [h1, h2, kiCompact_appendEmpty hput.ne, kiCompact_kiPut hwf c rev hc]
  rw [kiPut_gens_of_ne hne, getLastD_append_singleton]
  unfold tombZ
  rw [genPut_revs, List.getLastD_eq_getLast?, List.getLast?_append, List.getLast?_singleton]
  all_goals first | omega | (simp; omega) | simp

theorem kiLastEmpty_kiPut (ki : KeyIndex) (rev : Rev) : kiLastEmpty (kiPut ki rev) = false := by
  unfold kiLastEmpty
  rw [kiPut_gens, getLastD_append_singleton, genPut_revs]
  simp

theorem kiIsEmpty_kiPut (ki : KeyIndex) (rev : Rev) : kiIsEmpty (kiPut ki rev) = false := by
  cases h : kiIsEmpty (kiPut ki rev)
  · rfl
  · have := kiIsEmpty_lastEmpty h; rw [kiLastEmpty_kiPut] at this; cases this

theorem kiIsEmpty_kiTombstone (ki : KeyIndex) (rev : Rev) : kiIsEmpty (kiTombstone ki rev) = false := by
  unfold kiIsEmpty
  split
  · rename_i g hg
    rw [kiTombstone_gens, kiPut_gens] at hg
    have := congrArg List.length hg
    simp at this
  · rfl

theorem kiCompact_kiPut_fresh {ki : KeyIndex} (hwf : KiWf ki) (c : w64) (rev : Rev)
    (hc : sint.Z c < sint.Z rev.main) (he : kiIsEmpty (kiCompact c ki) = true) :
    kiCompact c (kiPut ki rev) = kiPut KeyIndex.fresh rev := by
  rw [kiCompact_kiPut hwf c rev hc]
  have hne := hwf.ne
  have hlt := compactGenIdx_lt c ki.gens hne
  unfold kiIsEmpty at he
  split at he
  · rename_i x hx
    simp only [decide_eq_true_eq] at he
    have hx0 : (kiCompact c ki).gens.getD 0 Gen.empty = x := by rw [hx]; rfl
    rw [kiCompact_gens, dropSet_getD0 _ _ _ _ hlt] at hx0
    have hver : x.ver = W64 0 := by
      rw [← hx0, cutGen_ver]
      have hmem : ki.gens.getD (compactGenIdx c ki.gens) Gen.empty ∈ ki.gens := by
        rw [getD_lt _ hlt]; exact List.getElem_mem hlt
      have hw := hwf.gens _ hmem
      rw [hw.1]
      have : (ki.gens.getD (compactGenIdx c ki.gens) Gen.empty).revs = [] :=
        (cutGen_revs_ne c _).1 (by rw [hx0]; exact he)
      rw [this]; rfl
    refine KeyIndex.ext' rfl ?_
    rw [kiPut_gens, kiPut_gens, hx]
    simp [gensOrEmpty, genPut, he, hver, Gen.empty, KeyIndex.fresh]
  · cases he

/-! ### The theorems, for a log's key index -/

theorem kiCompact_kiEmpty (c : w64) : kiCompact c kiEmpty = kiEmpty := by
  refine KeyIndex.ext' rfl ?_
  simp [kiCompact, kiEmpty, compactGenIdx, Gen.empty]

theorem kiIsEmpty_kiEmpty : kiIsEmpty kiEmpty = true := rfl

theorem idxGet_some_mem {idx : IndexM} (hs : idx.Pairwise idxLess) {k : GoString} {ki : KeyIndex}
    (h : idxGet idx k = some ki) : (k, ki) ∈ idx := by
  rw [idxGet_eq_find? idx hs] at h
  cases hf : idx.find? (fun z => decide (z.1 = k)) with
  | none => rw [hf] at h; cases h
  | some z =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    have hz := List.mem_of_find?_eq_some hf
    have hk : z.1 = k := by simpa using List.find?_some hf
    rw [← h, ← hk]; exact hz

/-! ### What compaction keeps -/

theorem kiFindGenAux_spec {gens : List Gen} {a : w64} : ∀ (fuel gx : Nat),
    kiFindGenAux gens a fuel = some gx →
    gx < fuel ∧ (gens.getD gx Gen.empty).revs ≠ [] ∧
      ¬ (gx ≠ gens.length - 1 ∧ sint.Z ((gens.getD gx Gen.empty).revs.getLastD Rev.zero).main ≤ sint.Z a) ∧
      sint.Z ((gens.getD gx Gen.empty).revs.headD Rev.zero).main ≤ sint.Z a
  | 0, gx, h => by simp [kiFindGenAux] at h
  | cg + 1, gx, h => by
    rw [kiFindGenAux_succ] at h
    simp only at h
    split at h
    · have := kiFindGenAux_spec cg gx h; exact ⟨by omega, this.2⟩
    · rename_i hne
      split at h
      · cases h
      · rename_i hnot
        split at h
        · rename_i hf; cases h; exact ⟨by omega, hne, hnot, hf⟩
        · have := kiFindGenAux_spec cg gx h; exact ⟨by omega, this.2⟩

theorem change_of_tomb {e : Ev} {k : GoString} (hk : e.key = k) (ht : e.tomb = true) :
    e.change = .del k := by
  cases hc : e.change with
  | put k' v l => simp [Ev.tomb, hc, Change.isDel] at ht
  | del k' => simp [Ev.key, hc, Change.key] at hk; rw [hk]

theorem change_of_not_tomb {e : Ev} {k : GoString} (hk : e.key = k) (ht : e.tomb = false) :
    ∃ v l, e.change = .put k v l := by
  cases hc : e.change with
  | put k' v l => simp [Ev.key, hc, Change.key] at hk; exact ⟨v, l, by rw [hk]⟩
  | del k' => simp [Ev.tomb, hc, Change.isDel] at ht

theorem revBytes_rev_inj {a b : Rev} {ta tb : Bool} (h : revBytes a ta = revBytes b tb) : a = b :=
  (revBytes_inj a b ta tb h).2

theorem compactGenIdx_appendEmpty {G : List Gen} (hne : G ≠ []) (c : w64)
    (hlast : ¬ tombZ (G.getLastD Gen.empty) < sint.Z c) :
    compactGenIdx c (G ++ [Gen.empty]) = compactGenIdx c G := by
  have hlt := compactGenIdx_lt c G hne
  apply compactGenIdx_eq
  · simp; omega
  · intro j hj
    rw [getD_append_lt _ _ _ _ (by omega)]
    exact compactGenIdx_before c G j hj
  · right
    rw [getD_append_lt _ _ _ _ hlt]
    rcases compactGenIdx_stop c G hne with h | h
    · rw [getLastD_eq_getD _ _ hne, show G.length - 1 = compactGenIdx c G by omega] at hlast
      exact hlast
    · exact h

theorem kiAvail_kiPut {ki : KeyIndex} (hwf : KiWf ki) (c : w64) (rev : Rev)
    (hc : sint.Z c < sint.Z rev.main) : kiAvail c (kiPut ki rev) = kiAvail c ki := by
  have hne := hwf.ne
  have hlt := compactGenIdx_lt c ki.gens hne
  unfold kiAvail
  simp only []
  rw [kiPut_gens_of_ne hne, compactGenIdx_put hwf]
  by_cases hl : compactGenIdx c ki.gens + 1 = ki.gens.length
  · rw [show compactGenIdx c ki.gens = ki.gens.length - 1 by omega, getD_dropLast_append_last _ _ _ hne,
      genPut_revs, genWalk_append_true _ _ _ (by simp [pAbove]; omega), getLastD_eq_getD _ _ hne]
    split
    · rfl
    · rename_i hw
      have := genWalk_range (ki.gens.getD (ki.gens.length - 1) Gen.empty).revs (pAbove c)
      rw [getD_append_lt _ _ _ _ (by omega)]
  · rw [getD_dropLast_append_lt _ _ _ _ (by omega)]

theorem kiAvail_kiTombstone {ki : KeyIndex} (hwf : KiWf ki) (c : w64) (rev : Rev)
    (hc : sint.Z c < sint.Z rev.main) : kiAvail c (kiTombstone ki rev) = kiAvail c ki := by
  rw [← kiAvail_kiPut hwf c rev hc]
  have hput := hwf.put rev
  have hlast : ¬ tombZ ((kiPut ki rev).gens.getLastD Gen.empty) < sint.Z c := by
    rw [kiPut_gens_of_ne hwf.ne, getLastD_append_singleton]
    unfold tombZ
    rw [genPut_revs, List.getLastD_eq_getLast?, List.getLast?_append, List.getLast?_singleton]
    all_goals first | omega | (simp; omega) | simp
  have hlt := compactGenIdx_lt c (kiPut ki rev).gens hput.ne
  unfold kiAvail
  simp only []
  rw [kiTombstone_gens, compactGenIdx_appendEmpty hput.ne c hlast, getD_append_lt _ _ _ _ hlt]

theorem kiAvail_kiApply {ki : KeyIndex} (hwf : KiWf ki) (c : w64) (e : Ev)
    (hc : sint.Z c < sint.Z e.rev.main) : kiAvail c (kiApply ki e) = kiAvail c ki := by
  unfold kiApply
  split
  · split
    · rfl
    · exact kiAvail_kiTombstone hwf c _ hc
  · exact kiAvail_kiPut hwf c _ hc

theorem kiAvail_fold (c : w64) (k : GoString) : ∀ (B : List Ev) (ki : KeyIndex), KiWf ki →
    (∀ e ∈ B, sint.Z c < sint.Z e.rev.main) → kiAvail c (kiFold ki B k) = kiAvail c ki
  | [], _, _, _ => rfl
  | e :: B, ki, hwf, hB => by
    rw [kiFold_cons]
    have hB' : ∀ x ∈ B, sint.Z c < sint.Z x.rev.main := fun x hx => hB x (List.mem_cons_of_mem _ hx)
    split
    · rw [kiAvail_fold c k B _ (kiApply_wf hwf e) hB', kiAvail_kiApply hwf c e (hB e List.mem_cons_self)]
    · exact kiAvail_fold c k B ki hwf hB'

theorem kiAvail_kiCompact_S {ki : KeyIndex} (hwf : KiWf ki) (c c' : w64) (hcc : sint.Z c ≤ sint.Z c') :
    kiAvail c' (kiCompact c ki) = kiAvail c' ki := by
  obtain ⟨hge, hidx⟩ := compactGenIdx_compact_ge hwf c c' hcc
  have hlt := compactGenIdx_lt c ki.gens hwf.ne
  unfold kiAvail
  simp only []
  rw [hidx, kiCompact_gens c ki]
  generalize compactGenIdx c ki.gens = gi at *
  generalize compactGenIdx c' ki.gens = m at *
  rcases Nat.lt_or_eq_of_le hge with hgt | heq
  · rw [show m - gi = (m - gi - 1) + 1 by omega, dropSet_getDs, show gi + (m - gi - 1) + 1 = m by omega]
  · subst heq
    rw [Nat.sub_self, dropSet_getD0 _ _ _ _ hlt]
    generalize ki.gens.getD gi Gen.empty = g
    rcases cutGen_cases c g with h | ⟨j, hj, -, hm, hr, -⟩
    · rw [h]
    · have hw' : (j : Int) ≤ genWalk g.revs (pAbove c') := genWalk_ge hj (by simp [pAbove]; omega)
      rw [hr, genWalk_drop hw', ite_eq_right (by omega), ite_eq_right (by omega)]
      congr 1
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
      congr 2; omega

/-- **(a) A compacted key index answers as the uncompacted one at or above the compaction
revision.** -/
theorem kiGet_kiCompact (log : Log) (hb : LogB log) (k : GoString) (c atRev : w64)
    (hc : sint.Z c ≤ sint.Z atRev) :
    kiGet (kiCompact c (kiOfKey (evsOf log) k)) atRev = kiGet (kiOfKey (evsOf log) k) atRev :=
  kiGet_kiCompact_S (kiOfKey_KiS log hb k) c atRev hc

/-- **(b) A key index compaction empties has no answer at or above the compaction revision.** -/
theorem kiGet_of_kiCompact_empty (log : Log) (hb : LogB log) (k : GoString) (c atRev : w64)
    (hc : sint.Z c ≤ sint.Z atRev) (he : kiIsEmpty (kiCompact c (kiOfKey (evsOf log) k)) = true) :
    kiGet (kiOfKey (evsOf log) k) atRev = none := by
  rw [← kiGet_kiCompact log hb k c atRev hc]; exact kiGet_isEmpty he atRev

/-- Compaction at `-1` (no compaction) changes nothing. -/
theorem kiCompact_neg (log : Log) (hb : LogB log) (k : GoString) :
    kiCompact (W64 (-1)) (kiOfKey (evsOf log) k) = kiOfKey (evsOf log) k :=
  kiCompact_neg_S (kiOfKey_KiS log hb k)

/-- Compactions compose: a later compaction at a higher revision is that compaction alone (the
job's per-key pass over a key a writer or an earlier pass changed). -/
theorem kiCompact_kiCompact (log : Log) (hb : LogB log) (k : GoString) (c c' : Int)
    (hc0 : -1 ≤ c) (h : c ≤ c') (hc' : c' < 2 ^ 63) :
    kiCompact (W64 c') (kiCompact (W64 c) (kiOfKey (evsOf log) k)) =
      kiCompact (W64 c') (kiOfKey (evsOf log) k) :=
  kiCompact_kiCompact_S (kiOfKey_KiS log hb k).wf _ _ (by word)

/-- A compaction at a lower revision after one at a higher revision changes nothing. -/
theorem kiCompact_kiCompact_le (log : Log) (hb : LogB log) (k : GoString) (c c' : Int)
    (hc0 : -1 ≤ c') (h : c' ≤ c) (hc : c < 2 ^ 63) :
    kiCompact (W64 c') (kiCompact (W64 c) (kiOfKey (evsOf log) k)) =
      kiCompact (W64 c) (kiOfKey (evsOf log) k) :=
  kiCompact_kiCompact_le_S (kiOfKey_KiS log hb k).wf _ _ (by word)

/-- A compaction leaves the last generation's emptiness (`tombstone`'s test). -/
theorem kiCompact_lastEmpty (log : Log) (hb : LogB log) (k : GoString) (c : Int) (hc0 : -1 ≤ c)
    (hc : c < 2 ^ 63) :
    kiLastEmpty (kiCompact (W64 c) (kiOfKey (evsOf log) k)) = kiLastEmpty (kiOfKey (evsOf log) k) := by
  -- (the bounds are not needed: any revision works)
  have _ := hc0; have _ := hc
  exact kiCompact_lastEmpty_S (kiOfKey_KiS log hb k).wf _

/-- A key index a compaction empties had an empty last generation. -/
theorem kiCompact_empty_lastEmpty (log : Log) (hb : LogB log) (k : GoString) (c : Int)
    (hc0 : -1 ≤ c) (hc : c < 2 ^ 63)
    (he : kiIsEmpty (kiCompact (W64 c) (kiOfKey (evsOf log) k)) = true) :
    kiLastEmpty (kiOfKey (evsOf log) k) = true := by
  rw [← kiCompact_lastEmpty log hb k c hc0 hc]; exact kiIsEmpty_lastEmpty he

/-- **Compaction commutes with the writer's next event** (above the compaction revision): the
compacted key index after the event is the code's `put`/`tombstone` on the compacted one (a
fresh one if the compaction had emptied it, `treeIndex.Put`; nothing if a tombstone finds it
absent, `treeIndex.Tombstone`'s `ErrRevisionNotFound`). -/
theorem kiCompactO_step (ilog : Log) (pend : List Change) (x : Change)
    (hb : LogB (ilog ++ [pend ++ [x]])) (k : GoString) (c : Int) (hc0 : -1 ≤ c)
    (hc : c < ilog.length) :
    kiCompactO c (kiOfKey (evsOf (ilog ++ [pend ++ [x]])) k) =
      (let ev := evOfChange ilog.length pend.length x
       if ev.key = k then
         match kiCompactO c (kiOfKey (evsOf (ilog ++ [pend])) k) with
         | some ki' =>
           if ev.tomb then (if kiLastEmpty ki' then some ki' else some (kiTombstone ki' ev.rev))
           else some (kiPut ki' ev.rev)
         | none => if ev.tomb then none else some (kiPut KeyIndex.fresh ev.rev)
       else kiCompactO c (kiOfKey (evsOf (ilog ++ [pend])) k)) := by
  have hlen : ilog.length + 1 < 2 ^ 63 := by have := hb.1; simp at this; omega
  have hpl : (pend ++ [x]).length < 2 ^ 63 := hb.2 _ (by simp)
  have hb' : LogB (ilog ++ [pend]) :=
    ⟨by simp; omega, fun cs hcs => by
      rcases List.mem_append.1 hcs with h | h
      · exact hb.2 cs (List.mem_append_left _ h)
      · rw [List.mem_singleton] at h; rw [h]; simp at hpl; omega⟩
  have hwf := (kiOfKey_KiS (ilog ++ [pend]) hb' k).wf
  rw [evsOf_append_change, kiOfKey_append]
  simp only []
  generalize hki : kiOfKey (evsOf (ilog ++ [pend])) k = ki at *
  have hcr : sint.Z (W64 c) < sint.Z (evOfChange ilog.length pend.length x).rev.main := by
    simp only [evOfChange]; word
  generalize evOfChange ilog.length pend.length x = ev at *
  by_cases hk : ev.key = k
  · rw [ite_eq_left hk, ite_eq_left hk]
    unfold kiApply
    by_cases hE : kiIsEmpty (kiCompact (W64 c) ki) = true
    · have hle : kiLastEmpty ki = true := by
        rw [← kiCompact_lastEmpty_S hwf]; exact kiIsEmpty_lastEmpty hE
      have hO : kiCompactO c ki = none := by unfold kiCompactO; rw [ite_eq_left hE]
      rw [hO]
      by_cases ht : ev.tomb = true
      · simp only [ht, hle, ↓reduceIte, hO]
      · simp only [ht, Bool.false_eq_true, ↓reduceIte]
        unfold kiCompactO
        rw [kiCompact_kiPut_fresh hwf _ _ hcr hE, kiIsEmpty_kiPut]
        rfl
    · have hO : kiCompactO c ki = some (kiCompact (W64 c) ki) := by
        unfold kiCompactO; rw [ite_eq_right hE]
      rw [hO]
      by_cases ht : ev.tomb = true
      · simp only [ht, ↓reduceIte, kiCompact_lastEmpty_S hwf]
        by_cases hle : kiLastEmpty ki = true
        · simp only [hle, ↓reduceIte, hO]
        · simp only [hle, Bool.false_eq_true, ↓reduceIte]
          unfold kiCompactO
          rw [kiCompact_kiTombstone hwf _ _ hcr, kiIsEmpty_kiTombstone]
          rfl
      · simp only [ht, Bool.false_eq_true, ↓reduceIte]
        unfold kiCompactO
        rw [kiCompact_kiPut hwf _ _ hcr, kiIsEmpty_kiPut]
        rfl
  · rw [ite_eq_right hk, ite_eq_right hk]

/-! ### The index: every key compacted at a level of its own -/

/-- The index `idx` holds the events `evs`, each key's index compacted at a level `c`,
`-1 ≤ c ≤ cmax` (absent if that compaction emptied it): `IdxRep`'s compacted form. -/
def IdxCRep (cmax : Int) (evs : List Ev) (idx : IndexM) : Prop :=
  idx.Pairwise idxLess ∧
    ∀ k, ∃ c : Int, -1 ≤ c ∧ c ≤ cmax ∧ idxGet idx k = kiCompactO c (kiOfKey evs k)

theorem IdxCRep.nil {cmax : Int} (h : -1 ≤ cmax) : IdxCRep cmax [] [] :=
  ⟨List.Pairwise.nil, fun k => ⟨-1, Int.le_refl _, h, by
    simp only [kiOfKey_nil]
    unfold kiCompactO
    rfl⟩⟩

theorem IdxCRep.mono {cmax cmax' : Int} {evs : List Ev} {idx : IndexM} (h : IdxCRep cmax evs idx)
    (hle : cmax ≤ cmax') : IdxCRep cmax' evs idx :=
  ⟨h.1, fun k => by
    obtain ⟨c, h0, h1, h2⟩ := h.2 k
    exact ⟨c, h0, Int.le_trans h1 hle, h2⟩⟩

/-- The uncompacted index is a compacted one (every level `-1`). -/
theorem IdxCRep.of_indexOf (log : Log) (hb : LogB log) {cmax : Int} (h : -1 ≤ cmax) :
    IdxCRep cmax (evsOf log) (indexOf (evsOf log)) := by
  refine ⟨indexOf_sorted _, fun k => ⟨-1, Int.le_refl _, h, ?_⟩⟩
  unfold kiCompactO
  rw [show ((-1 : Int)) = -1 from rfl, kiCompact_neg log hb k]
  have hrep := (indexOf_rep (evsOf log)).2 k
  cases hg : idxGet (indexOf (evsOf log)) k with
  | none =>
    rw [hg] at hrep
    simp only [Option.getD_none] at hrep
    rw [← hrep, kiIsEmpty_kiEmpty]; rfl
  | some ki =>
    rw [hg] at hrep
    simp only [Option.getD_some] at hrep
    have hmem := idxGet_some_mem (indexOf_sorted _) hg
    have hh := indexOf_head' (evsOf log) (k, ki) hmem
    rw [← hrep, (kiIsEmpty_false_of_head hh).1]; rfl

/-- A key the index has: its key index of the events compacted at its level, not empty. -/
theorem IdxCRep.get_some {cmax : Int} {evs : List Ev} {idx : IndexM} (h : IdxCRep cmax evs idx)
    {k : GoString} {ki : KeyIndex} (hg : idxGet idx k = some ki) :
    ∃ c : Int, -1 ≤ c ∧ c ≤ cmax ∧ ki = kiCompact (W64 c) (kiOfKey evs k) ∧ kiIsEmpty ki = false := by
  obtain ⟨c, h0, h1, h2⟩ := h.2 k
  refine ⟨c, h0, h1, ?_⟩
  rw [hg] at h2
  unfold kiCompactO at h2
  split at h2
  · cases h2
  · rename_i hne
    cases h2
    exact ⟨rfl, by simpa using hne⟩

/-- A key the index does not have: its compaction at its level emptied it. -/
theorem IdxCRep.get_none {cmax : Int} {evs : List Ev} {idx : IndexM} (h : IdxCRep cmax evs idx)
    {k : GoString} (hg : idxGet idx k = none) :
    ∃ c : Int, -1 ≤ c ∧ c ≤ cmax ∧ kiIsEmpty (kiCompact (W64 c) (kiOfKey evs k)) = true := by
  obtain ⟨c, h0, h1, h2⟩ := h.2 k
  refine ⟨c, h0, h1, ?_⟩
  rw [hg] at h2
  unfold kiCompactO at h2
  split at h2
  · assumption
  · cases h2

/-- **The writer's next event** keeps the representation (its revision is above every level). -/
theorem IdxCRep.step (ilog : Log) (pend : List Change) (x : Change)
    (hb : LogB (ilog ++ [pend ++ [x]])) {cmax : Int} {idx : IndexM} (hcmax : cmax < ilog.length)
    (h : IdxCRep cmax (evsOf (ilog ++ [pend])) idx) :
    IdxCRep cmax (evsOf (ilog ++ [pend ++ [x]]))
      (idxApply idx (evOfChange ilog.length pend.length x)) := by
  obtain ⟨hs, hk⟩ := h
  have hstep := fun k c hc0 hc => kiCompactO_step ilog pend x hb k c hc0 hc
  generalize hev : evOfChange ilog.length pend.length x = ev at hstep
  have hevs : evsOf (ilog ++ [pend ++ [x]]) = evsOf (ilog ++ [pend]) ++ [ev] := by
    rw [evsOf_append_change, hev]
  rw [← hev] at ⊢
  rw [hev]
  unfold idxApply
  by_cases ht : ev.tomb = true
  · simp only [ht, ↓reduceIte]
    rw [idxTombstone_eq]
    obtain ⟨c0, h0, h1, h2⟩ := hk ev.key
    by_cases hle : kiLastEmpty ((idxGet idx ev.key).getD kiEmpty) = true
    · rw [ite_eq_left hle]
      refine ⟨hs, fun k => ?_⟩
      by_cases hkk : ev.key = k
      · subst hkk
        refine ⟨c0, h0, h1, ?_⟩
        rw [h2, hstep ev.key c0 h0 (by omega)]
        simp only [↓reduceIte]
        rw [h2] at hle
        cases ho : kiCompactO c0 (kiOfKey (evsOf (ilog ++ [pend])) ev.key) with
        | none => simp [ht]
        | some ki' =>
          rw [ho] at hle
          simp only [Option.getD_some] at hle
          simp [ht, hle]
      · obtain ⟨c, hc0, hc1, hc2⟩ := hk k
        refine ⟨c, hc0, hc1, ?_⟩
        rw [hc2, hstep k c hc0 (by omega)]
        simp only [ite_eq_right hkk]
    · rw [ite_eq_right hle]
      refine ⟨btInsert_sorted idxLess_swo hs, fun k => ?_⟩
      rw [idxGet_btInsert hs]
      by_cases hkk : ev.key = k
      · subst hkk
        refine ⟨c0, h0, h1, ?_⟩
        rw [ite_eq_left rfl, hstep ev.key c0 h0 (by omega)]
        simp only [↓reduceIte]
        rw [h2] at hle ⊢
        cases ho : kiCompactO c0 (kiOfKey (evsOf (ilog ++ [pend])) ev.key) with
        | none => rw [ho] at hle; simp [kiLastEmpty_kiEmpty] at hle
        | some ki' =>
          rw [ho] at hle
          simp only [Option.getD_some] at hle ⊢
          simp [ht, hle]
      · rw [ite_eq_right hkk]
        obtain ⟨c, hc0, hc1, hc2⟩ := hk k
        refine ⟨c, hc0, hc1, ?_⟩
        rw [hc2, hstep k c hc0 (by omega)]
        simp only [ite_eq_right hkk]
  · simp only [ht, Bool.false_eq_true, ↓reduceIte]
    rw [idxPut_eq]
    refine ⟨btInsert_sorted idxLess_swo hs, fun k => ?_⟩
    rw [idxGet_btInsert hs]
    obtain ⟨c, hc0, hc1, hc2⟩ := hk k
    refine ⟨c, hc0, hc1, ?_⟩
    rw [hstep k c hc0 (by omega)]
    simp only []
    by_cases hkk : ev.key = k
    · subst hkk
      rw [ite_eq_left rfl, ite_eq_left rfl, hc2]
      cases ho : kiCompactO c (kiOfKey (evsOf (ilog ++ [pend])) ev.key) with
      | none => simp [ht, kiPut_fresh]
      | some ki' => simp [ht]
    · rw [ite_eq_right hkk, ite_eq_right hkk, hc2]

/-- **A reader at or above every level** reads the uncompacted index's answer. -/
theorem IdxCRep.kiAt (log : Log) (hb : LogB log) {cmax : Int} {idx : IndexM}
    (h : IdxCRep cmax (evsOf log) idx) (atRev : w64) (hc : cmax ≤ sint.Z atRev) (k : GoString) :
    kiGet (kiAt idx k) atRev = kiGet (kiOfKey (evsOf log) k) atRev := by
  obtain ⟨c, hc0, hc1, hc2⟩ := h.2 k
  have hca : sint.Z (W64 c) ≤ sint.Z atRev := by
    have : sint.Z atRev < 2 ^ 63 := by word
    have : sint.Z (W64 c) = c := by word
    omega
  unfold mvcc.kiAt
  rw [hc2]
  unfold kiCompactO
  split
  · rename_i he
    rw [Option.getD_none, kiGet_kiEmpty, kiGet_of_kiCompact_empty log hb k _ atRev hca he]
  · rw [Option.getD_some, kiGet_kiCompact log hb k _ atRev hca]

/-- **A range read at or above every level** reads the uncompacted index's answers (a key the
compaction removed has none there). -/
theorem IdxCRep.rangeAt (log : Log) (hb : LogB log) {cmax : Int} {idx : IndexM}
    (h : IdxCRep cmax (evsOf log) idx) (atRev : w64) (hc : cmax ≤ sint.Z atRev) (k e : GoString) :
    rangeAt idx k e atRev = rangeAt (indexOf (evsOf log)) k e atRev := by
  rw [rangeAt_eq_keys _ h.1, rangeAt_eq_keys _ (indexOf_sorted _)]
  have hans : ∀ key, kiGet (mvcc.kiAt idx key) atRev = kiGet (mvcc.kiAt (indexOf (evsOf log)) key) atRev := by
    intro key; rw [kiAt_indexOf]; exact h.kiAt log hb atRev hc key
  simp only [hans]
  -- a key the compaction emptied has no answer at `atRev`
  have habsent : ∀ key, idxGet idx key = none → kiGet (kiOfKey (evsOf log) key) atRev = none := by
    intro key hg
    obtain ⟨c, hc0, hc1, hc2⟩ := h.2 key
    rw [hg] at hc2
    unfold kiCompactO at hc2
    split at hc2
    · rename_i he
      have : sint.Z atRev < 2 ^ 63 := by word
      have hw : sint.Z (W64 c) = c := by word
      exact kiGet_of_kiCompact_empty log hb key _ atRev (by omega) he
    · cases hc2
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
    obtain ⟨c, hc0, hc1, hc2⟩ := h.2 z.1
    rw [hg] at hc2
    intro hE
    rw [hE] at hc2
    unfold kiCompactO at hc2
    rw [kiCompact_kiEmpty, ite_eq_left kiIsEmpty_kiEmpty] at hc2
    cases hc2
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

/-! ### The bucket: what compaction keeps, what it may delete -/

/-- Revision `c` does not delete a key and then put it again (`issues/
etcd-compaction-delete-then-put.md`: compaction at `c` would drop the put, the key's live
revision). The server's transaction checks (`checkIntervals`) ensure it. -/
def NoDelPutAt (log : Log) (c : Int) : Prop :=
  ∀ (cs : List Change) (i j : Nat) (k v : GoString) (l : w64), 0 ≤ c → log[c.toNat]? = some cs →
    i < j → cs[i]? = some (.del k) → cs[j]? = some (.put k v l) → False

/-- Compaction at `c` keeps the revision `r`: some key's `doCompact` makes it available. -/
def keepAt (log : Log) (c : Int) (r : Rev) : Prop :=
  ∃ k, kiAvail (W64 c) (kiOfKey (evsOf log) k) = some r

/-- **A bucket key compaction at `c` may delete** (of a log with revision `c`): a revision's
bytes, with a main at or below `c`, that compaction does not keep (what the job deletes: the
keys of the range `[_, c + 1)` not in `treeIndex.Compact`'s `available`). A read at or above
`c` never names one when revision `c` does not delete and put a key again (`named_not_del`'s
premise `NoDelPutAt`); when it does, the read can name one: the bug of
`issues/etcd-compaction-delete-then-put.md`. -/
def KeyDel (log : Log) (c : Int) (key : GoString) : Prop :=
  c < log.length ∧
    ∃ (r : Rev) (t : Bool), key = revBytes r t ∧ 0 ≤ sint.Z r.main ∧ sint.Z r.main ≤ c ∧
      ¬ keepAt log c r

/-- No compaction (`c < 0`) deletes nothing. -/
theorem KeyDel_neg {log : Log} {c : Int} {key : GoString} (h : c < 0) : ¬ KeyDel log c key := by
  rintro ⟨-, r, t, -, h0, h1, -⟩
  omega

/-- **What a read names is kept**: the revision a read at or above `c` answers, if its main is at
or below `c`, is the one compaction keeps for the key. -/
theorem kiGet_avail (log : Log) (hb : LogB log) (c : Int) (hc0 : -1 ≤ c) (hc : c < log.length)
    (hnd : NoDelPutAt log c) (k : GoString) (atRev : w64) (hca : c ≤ sint.Z atRev)
    (r cr : Rev) (v : w64) (hget : kiGet (kiOfKey (evsOf log) k) atRev = some (r, cr, v))
    (hr : sint.Z r.main ≤ c) :
    kiAvail (W64 c) (kiOfKey (evsOf log) k) = some r := by
  have hs := kiOfKey_KiS log hb k
  have hev := (kiOfKey_struct k (evsOf log)).2.2
  have hord := evsOf_ord log hb
  have hcw : sint.Z (W64 c) = c := by have := hb.1; word
  generalize hki : kiOfKey (evsOf log) k = ki at *
  unfold kiGet at hget
  split at hget
  · cases hget
  rename_i gx hfg
  obtain ⟨hgxlt, hne, hnot, hhead⟩ := kiFindGenAux_spec ki.gens.length gx hfg
  generalize hg : ki.gens.getD gx Gen.empty = g at *
  simp only at hget
  rw [ite_eq_right hne] at hget
  rcases genWalk_pAbove_spec g.revs atRev with ⟨hw, -⟩ | ⟨j, hj, hw, hjm, hjafter⟩
  · simp [hw] at hget
  rw [hw] at hget
  simp only [Int.toNat_natCast] at hget
  rw [ite_eq_right (by omega)] at hget
  simp only [Option.some.injEq, Prod.mk.injEq] at hget
  obtain ⟨hrj, -, -⟩ := hget
  rw [getD_lt _ hj] at hrj
  subst hrj
  have hrmem : g.revs[j] ∈ (ki.gens.getD gx Gen.empty).revs := by rw [hg]; exact List.getElem_mem hj
  -- `r` is not a tombstone
  have hnottomb : ¬ (gx + 1 < ki.gens.length ∧ j + 1 = g.revs.length) := by
    rintro ⟨h1, h2⟩
    apply hnot
    refine ⟨by omega, ?_⟩
    have hl : g.revs.getLastD Rev.zero = g.revs[j] := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
      simp only [show g.revs.length - 1 = j by omega]; rfl
    rw [hl]; exact hjm
  have hidx : compactGenIdx (W64 c) ki.gens = gx := by
    apply compactGenIdx_eq _ _ _ hgxlt
    · intro j' hj'
      have hne' : (ki.gens.getD j' Gen.empty).revs ≠ [] := hs.wf.nonlast j' (by omega)
      have htm := getLastD_mem _ Rev.zero hne'
      have hlt := hs.cross hj' hgxlt htm hrmem
      unfold tombZ
      rw [hcw]
      have hle := Rev.lt_main_le hlt
      rcases Int.lt_or_eq_of_le (Int.le_trans hle hr) with h1 | h1
      · exact h1
      exfalso
      -- a delete and a put of the key in revision `c`
      generalize ht : (ki.gens.getD j' Gen.empty).revs.getLastD Rev.zero = tomb at *
      have hlenj := List.length_pos_iff.2 hne'
      have hgj : ki.gens[j']? = some (ki.gens.getD j' Gen.empty) := by
        rw [List.getElem?_eq_getElem (by omega), getD_lt _ (by omega)]
      have htp : (ki.gens.getD j' Gen.empty).revs[(ki.gens.getD j' Gen.empty).revs.length - 1]? = some tomb := by
        rw [← ht, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
        rw [List.getElem?_eq_getElem (by omega)]; rfl
      obtain ⟨e1, he1, he1r, he1k, he1t⟩ := hev j' _ _ tomb hgj htp
      have he1t' : e1.tomb = true := he1t.2 ⟨by omega, by omega⟩
      have hgx : ki.gens[gx]? = some g := by rw [← hg, List.getElem?_eq_getElem hgxlt, getD_lt _ hgxlt]
      obtain ⟨e2, he2, he2r, he2k, he2t⟩ := hev gx j g _ hgx (List.getElem?_eq_getElem hj)
      have he2t' : e2.tomb = false := by
        cases h' : e2.tomb
        · rfl
        · exact absurd (he2t.1 h') hnottomb
      have hc1 := change_of_tomb he1k he1t'
      obtain ⟨v2, l2, hc2⟩ := change_of_not_tomb he2k he2t'
      obtain ⟨-, -, hs1, cs1, hl1, hcs1⟩ := hord.2 e1 he1
      obtain ⟨-, -, hs2, cs2, hl2, hcs2⟩ := hord.2 e2 he2
      rw [he1r] at hl1 hcs1 hs1
      rw [he2r] at hl2 hcs2 hs2
      have hmeq : tomb.main = g.revs[j].main := by
        have : sint.Z tomb.main = sint.Z g.revs[j].main := by omega
        word
      rw [hmeq] at hl1
      rw [hl1] at hl2; cases hl2
      have hsub : sint.Z tomb.sub < sint.Z g.revs[j].sub := by
        rcases hlt with h3 | ⟨-, h3⟩
        · omega
        · exact h3
      have hcn : c.toNat = g.revs[j].main.toNat := by
        have : sint.Z g.revs[j].main = c := by omega
        have h0 : 0 ≤ c := by have := hs.mem_nonneg hgxlt hrmem; omega
        word
      rw [hc1] at hcs1
      rw [hc2] at hcs2
      exact hnd cs1 tomb.sub.toNat g.revs[j].sub.toNat k v2 l2
        (by have := hs.mem_nonneg hgxlt hrmem; omega) (by rw [hcn]; exact hl1) (by word) hcs1 hcs2
    · by_cases hl : gx + 1 = ki.gens.length
      · exact Or.inl hl
      · right
        rw [hg]
        unfold tombZ
        rw [hcw]
        have : ¬ sint.Z (g.revs.getLastD Rev.zero).main ≤ sint.Z atRev := fun h' => hnot ⟨by omega, h'⟩
        omega
  unfold kiAvail
  simp only []
  rw [hidx, hg]
  have hwc : genWalk g.revs (pAbove (W64 c)) = j := by
    apply genWalk_eq_some j hj
    · simp only [pAbove, hcw, decide_eq_false_iff_not, Int.not_lt]; omega
    · intro k' hk' hjk'
      have := hjafter k' hk' hjk'
      simp only [pAbove, hcw, decide_eq_true_eq]; omega
  rw [hwc, ite_eq_right (by omega)]
  simp only [Int.toNat_natCast]
  rw [getD_lt _ hj]

/-- **A read at or above the compaction revision never names a key compaction may delete**, when
the compaction revision does not delete a key and put it again (`NoDelPutAt`: else it can,
`issues/etcd-compaction-delete-then-put.md`). -/
theorem named_not_del (log : Log) (hb : LogB log) (c : Int) (hc0 : -1 ≤ c)
    (hnd : NoDelPutAt log c) (k : GoString)
    (atRev : w64) (hca : c ≤ sint.Z atRev) (r cr : Rev) (v : w64)
    (hget : kiGet (kiOfKey (evsOf log) k) atRev = some (r, cr, v)) (t : Bool) :
    ¬ KeyDel log c (revBytes r t) := by
  rintro ⟨hc, r', t', hk, h0, h1, hkeep⟩
  have := revBytes_rev_inj hk
  subst this
  exact hkeep ⟨k, kiGet_avail log hb c hc0 hc hnd k atRev hca r cr v hget h1⟩

/-- What compaction at `c` keeps depends only on the log up to `c` (later revisions, above it,
do not change any key's choice). -/
theorem kiAvail_prefix (log log' : Log) (hpre : log <+: log') (hb' : LogB log') (c : Int)
    (hc0 : -1 ≤ c) (hc : c < log.length) (k : GoString) :
    kiAvail (W64 c) (kiOfKey (evsOf log') k) = kiAvail (W64 c) (kiOfKey (evsOf log) k) := by
  obtain ⟨t, rfl⟩ := hpre
  revert hb'
  refine snoc_induction (P := fun t => LogB (log ++ t) →
    kiAvail (W64 c) (kiOfKey (evsOf (log ++ t)) k) = kiAvail (W64 c) (kiOfKey (evsOf log) k)) ?_ ?_ t
  · intro _; rw [List.append_nil]
  intro t cs ih hb
  rw [← List.append_assoc] at hb ⊢
  rw [evsOf_append, kiOfKey_eq_kiFold, kiFold_append, ← kiOfKey_eq_kiFold]
  have hlen : (log ++ t).length + 1 < 2 ^ 63 := by have := hb.1; simp at this ⊢; omega
  rw [kiAvail_fold _ k _ _ (kiOfKey_struct k _).1]
  · exact ih hb.prefix
  · intro e he
    rw [evsOfRev_main _ cs e he]
    have hcb : c < 2 ^ 63 := by simp at hlen; omega
    have : sint.Z (W64 c) = c := by word
    have h2 : sint.Z (W64 ((log ++ t).length : Int)) = (log ++ t).length := by word
    rw [this, h2]; simp; omega

theorem KeyDel_prefix (log log' : Log) (hpre : log <+: log') (hb' : LogB log') (c : Int)
    (hc0 : -1 ≤ c) (hc : c < log.length) (key : GoString) :
    KeyDel log' c key ↔ KeyDel log c key := by
  have hlen : log.length ≤ log'.length := hpre.length_le
  have hkeep : ∀ r, keepAt log' c r ↔ keepAt log c r := by
    intro r; unfold keepAt
    simp only [kiAvail_prefix log log' hpre hb' c hc0 hc]
  unfold KeyDel
  simp only [hkeep]
  constructor
  · rintro ⟨-, h3⟩; exact ⟨hc, h3⟩
  · rintro ⟨-, h3⟩; exact ⟨by omega, h3⟩

/-- An earlier compaction of a key index does not change what a later one keeps. -/
theorem kiAvail_kiCompact (log : Log) (hb : LogB log) (k : GoString) (c c' : Int)
    (hc0 : -1 ≤ c) (h : c ≤ c') (hc' : c' < 2 ^ 63) :
    kiAvail (W64 c') (kiCompact (W64 c) (kiOfKey (evsOf log) k)) =
      kiAvail (W64 c') (kiOfKey (evsOf log) k) :=
  kiAvail_kiCompact_S (kiOfKey_KiS log hb k).wf _ _ (by word)

/-! ### Compaction-aware readers (2026-10-13, unit 6a)

`NoDelPutAt log c` depends only on revision `c` of the log (`NoDelPutAt_prefix`); a read at or
above a compaction revision `c'` names no key compaction at `c'` deletes, of any certified log
agreeing with the reader's up to `c'` (`rangeAnswers_not_del`: `named_not_del` through the
prefix order). -/

/-- No compaction (`c < 0`) needs nothing. -/
theorem NoDelPutAt_neg {log : Log} {c : Int} (h : c < 0) : NoDelPutAt log c := by
  intro _ _ _ _ _ _ h0; omega

/-- `NoDelPutAt` at `c` is a property of revision `c` alone: two logs in prefix order, both
with revision `c`, agree on it. -/
theorem NoDelPutAt_prefix {log log' : Log} (hpre : log <+: log') {c : Int}
    (hc : c < log.length) : NoDelPutAt log' c ↔ NoDelPutAt log c := by
  have hget : 0 ≤ c → log'[c.toNat]? = log[c.toNat]? := by
    intro h0
    obtain ⟨t, rfl⟩ := hpre
    rw [List.getElem?_append_left (by omega)]
  unfold NoDelPutAt
  constructor
  · intro h cs i j k v l h0 hl
    exact h cs i j k v l h0 (by rw [hget h0]; exact hl)
  · intro h cs i j k v l h0 hl
    exact h cs i j k v l h0 (by rw [← hget h0]; exact hl)

/-- An answer of a range read is its key's index's answer. -/
theorem rangeAnswers_get (log : Log) (endNil : Bool) (k e : GoString) (atRev : w64)
    (a : GoString × Rev × Rev × w64) (ha : a ∈ rangeAnswers log endNil k e atRev) :
    kiGet (kiOfKey (evsOf log) a.1) atRev = some a.2 := by
  obtain ⟨key, m, c, v⟩ := a
  simp only
  rw [← idxGet_indexOf_bind]
  cases endNil with
  | true =>
    rw [rangeAnswers_nil, Option.mem_toList] at ha
    cases hg : kiGet (kiOfKey (evsOf log) k) atRev with
    | none => rw [hg] at ha; simp at ha
    | some ans =>
      rw [hg] at ha
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      rw [idxGet_indexOf_bind]
      exact hg
  | false =>
    unfold rangeAnswers at ha
    simp only [Bool.false_eq_true, ↓reduceIte] at ha
    unfold rangeAt at ha
    rw [List.mem_filterMap] at ha
    obtain ⟨z, hz, hza⟩ := ha
    rw [List.mem_filter] at hz
    cases hg : kiGet z.2 atRev with
    | none => rw [hg] at hza; simp at hza
    | some ans =>
      rw [hg] at hza
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hza
      obtain ⟨rfl, rfl⟩ := hza
      rw [idxGet_of_mem _ (indexOf_sorted _) z hz.1]
      exact hg

/-- **A read at or above a compaction revision names no key that compaction deletes** (unit 6a):
the reader's log `log` extends a log `lc` with revision `c'`, the deleter's certified log `log'`
is in prefix order with `lc`, and revision `c'` of it does not delete then put a key
(`NoDelPutAt`, what the compactor asserted): an answer of a read of `log` at `atRev ≥ c'`, at
revision bytes of its modification, is not a key compaction at `c'` deletes (`KeyDel log' c'`). -/
theorem rangeAnswers_not_del (lc log log' : Log) (hpre : lc <+: log) (hb : LogB log)
    (hb' : LogB log') (hcmp : lc <+: log' ∨ log' <+: lc) (c' : Int) (hc0 : -1 ≤ c')
    (hc' : c' < lc.length) (hnd : NoDelPutAt log' c') (endNil : Bool) (k e : GoString)
    (atRev : w64) (hca : c' ≤ sint.Z atRev) (a : GoString × Rev × Rev × w64)
    (ha : a ∈ rangeAnswers log endNil k e atRev) (t : Bool) :
    ¬ KeyDel log' c' (revBytes a.2.1 t) := by
  intro hdel
  have hblc : LogB lc := hb.prefix' hpre
  -- the deleter's log and the reader's agree up to `c'`: through `lc`
  have hdel_lc : KeyDel lc c' (revBytes a.2.1 t) := by
    rcases hcmp with h | h
    · exact (KeyDel_prefix lc log' h hb' c' hc0 hc' _).1 hdel
    · exact (KeyDel_prefix log' lc h hblc c' hc0 hdel.1 _).2 hdel
  have hnd_lc : NoDelPutAt lc c' := by
    rcases hcmp with h | h
    · exact (NoDelPutAt_prefix h hc').1 hnd
    · exact (NoDelPutAt_prefix h hdel.1).2 hnd
  have hdel_log : KeyDel log c' (revBytes a.2.1 t) :=
    (KeyDel_prefix lc log hpre hb c' hc0 hc' _).2 hdel_lc
  have hnd_log : NoDelPutAt log c' := (NoDelPutAt_prefix hpre hc').2 hnd_lc
  exact named_not_del log hb c' hc0 hnd_log a.1 atRev hca a.2.1 a.2.2.1 a.2.2.2
    (rangeAnswers_get log endNil k e atRev a ha) t hdel_log

end mvcc
end EtcdGrove
end Perennial
