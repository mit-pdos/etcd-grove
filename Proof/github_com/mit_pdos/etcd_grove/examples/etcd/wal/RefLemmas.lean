/-
Lean-first (no Rocq counterpart).

# The tester's reference model against the WAL spec's (WAL W4c step 2; plan §2.5, §3)

Pure lemmas relating the transliteration of `ref.go` (`Defs.lean`) to `WalHist`'s vocabulary, through
`absOp`:

* **the reads commute with the abstraction** (`tReadCut_abs`): the tester's `walReadCut` of a history
  is, component by component, the model's of its abstraction (no bound needed: where the Go
  arithmetic subtracts, it does so above the base);
* **`walImgs` enumerates the images** (`tImgs_complete`): every image of the abstraction is the
  abstraction of a listed image;
* **the name bound** (`tNameBound_eq`): `nameBound` is `walNameBound … false` when no index is
  `2^64-1`; `openBound` bounds each image's (`tNameBound_le_openBound`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-! ## The hard state -/

theorem tHsEmpty_iff (h : THs) : tHsEmpty h = true ↔ hsEmptyP (absHs h) := by
  simp [tHsEmpty, hsEmptyP, absHs, and_assoc]

theorem absHs_phsNext (p h : THs) : absHs (tPhsNext p h) = phsNext (absHs p) (absHs h) := by
  unfold tPhsNext phsNext
  by_cases hh : tHsEmpty h = true
  · have := (tHsEmpty_iff h).1 hh
    simp only [hsEmptyP] at this
    simp only [hh, ite_true]; rw [if_pos this]
  · have : ¬ hsEmptyP (absHs h) := fun h' => hh ((tHsEmpty_iff h).2 h')
    simp only [Bool.not_eq_true] at hh
    simp only [hsEmptyP] at this
    simp only [hh, Bool.false_eq_true, ite_false]; rw [if_neg this]

theorem absHs_zero : absHs tHs0 = hsZero := rfl

/-- The abstraction's hard-state step. -/
theorem walLastHS_abs_step (p : THs) (o : TOp) :
    absHs (if o.snap then p else tPhsNext p o.hs) =
      (match absOp o with | .save h _ => phsNext (absHs p) h | .snap _ => absHs p) := by
  unfold absOp
  cases o.snap <;> simp [absHs_phsNext]

theorem tLastHS_abs (h : List TOp) : absHs (tLastHS h) = walLastHS (h.map absOp) := by
  unfold tLastHS walLastHS
  rw [List.foldl_map]
  suffices ∀ (l : List TOp) (p : THs), absHs (l.foldl (fun p o => if o.snap then p else tPhsNext p o.hs) p) =
      l.foldl (fun q o => match absOp o with | .save h _ => phsNext q h | .snap _ => q) (absHs p) by
    exact this h tHs0
  intro l
  induction l with
  | nil => intro p; rfl
  | cons o l ih =>
    intro p
    simp only [List.foldl_cons]
    rw [ih, walLastHS_abs_step]

theorem tLastHS_commit (h : List TOp) : (tLastHS h).commit' = (walLastHS (h.map absOp)).Commit' := by
  rw [← tLastHS_abs]; rfl

/-! ## The fold -/

/-- The tester's contents and the model's agree on what the tester reads. -/
def tAgree (s : TContents) (σ : StorContents) : Prop := absC s = projC σ

theorem tAgree_b {s : TContents} {σ : StorContents} (h : tAgree s σ) : uint.nat s.baseIdx = σ.b := by
  have := congrArg (fun x => x.2.1) h; simp [absC, projC] at this; simp [StorContents.b, this]

theorem tAgree_commit {s : TContents} {σ : StorContents} (h : tAgree s σ) :
    uint.nat s.hs.commit' = σ.commit := by
  have := congrArg (fun x => x.1) h; simp [absC, projC, absHs] at this
  simp [StorContents.commit, ← this]

theorem tAgree_ents {s : TContents} {σ : StorContents} (h : tAgree s σ) :
    s.ents.map absEnt = σ.ents := by
  have := congrArg (fun x => x.2.2.2) h; simpa [absC, projC] using this

theorem tReadEnt_abs (b : w64) (ents : List TEnt) (e : TEnt) :
    (tReadEnt b ents e).map (List.map absEnt) = readEnt (uint.nat b) (ents.map absEnt) (absEnt e) := by
  unfold tReadEnt readEnt
  simp only [absEnt, List.length_map]
  by_cases h1 : uint.nat e.index' ≤ uint.nat b
  · simp [h1]
  · have hsub : uint.nat (e.index' - b - W64 1) = uint.nat e.index' - uint.nat b - 1 := by word
    simp only [h1, ite_false, hsub]
    by_cases h2 : ents.length < uint.nat e.index' - uint.nat b - 1
    · simp [h2, Nat.not_le.mpr h2]
    · simp [h2, Nat.le_of_not_lt h2, List.map_take, absEnt]

theorem tReadEnts_abs (b : w64) (es : List TEnt) : ∀ (ents : List TEnt),
    (es.foldlM (fun ents e => tReadEnt b ents e) ents).map (List.map absEnt) =
      (es.map absEnt).foldlM (fun ents e => readEnt (uint.nat b) ents e) (ents.map absEnt) := by
  induction es with
  | nil => intro ents; rfl
  | cons e es ih =>
    intro ents
    simp only [List.foldlM_cons, List.map_cons]
    rw [← tReadEnt_abs]
    cases tReadEnt b ents e with
    | none => rfl
    | some x => simp only [Option.bind_some, Option.map_some]; exact ih x

theorem tSaveSnap_agree {s : TContents} {σ : StorContents} (h : tAgree s σ) (idx term : w64) :
    tAgree (tSaveSnap s idx term) (walSaveSnap σ (absSnapMd idx term)) := by
  have hb := tAgree_b h
  have hc := tAgree_commit h
  have he := tAgree_ents h
  have hI : (absSnapMd idx term).Index' = idx := rfl
  have hT : (absSnapMd idx term).Term' = term := rfl
  unfold tSaveSnap walSaveSnap
  by_cases h1 : uint.nat idx < uint.nat s.baseIdx
  · rw [if_pos h1, if_pos (show uint.nat (absSnapMd idx term).Index' < σ.b by rw [hI, ← hb]; exact h1)]
    exact h
  · rw [if_neg h1, if_neg (show ¬ uint.nat (absSnapMd idx term).Index' < σ.b by rw [hI, ← hb]; exact h1)]
    have hsub : uint.nat (idx - s.baseIdx) = uint.nat idx - uint.nat s.baseIdx := by word
    have hhs : absHs s.hs = σ.hs := by
      have := congrArg (fun x => x.1) h; simpa [absC, projC] using this
    by_cases h2 : uint.nat idx ≤ uint.nat s.hs.commit'
    · rw [if_pos h2, if_pos (show uint.nat (absSnapMd idx term).Index' ≤ σ.commit by rw [hI, ← hc]; exact h2)]
      unfold tAgree absC projC
      simp only [hhs, hI, hT, hsub, hb, List.map_drop, he]
    · rw [if_neg h2, if_neg (show ¬ uint.nat (absSnapMd idx term).Index' ≤ σ.commit by rw [hI, ← hc]; exact h2)]
      unfold tAgree absC projC
      simp only [hhs, hI, hT, List.map_nil]

theorem tFoldChkFrom_abs : ∀ (h : List TOp) (s : TContents) (σ : StorContents), tAgree s σ →
    (tFoldChkFrom s h).map absC = (walFoldChkFrom σ (h.map absOp)).map projC := by
  intro h
  induction h with
  | nil => intro s σ hs; exact congrArg some hs
  | cons o h ih =>
    intro s σ hs
    cases ho : o.snap with
    | true =>
      have hop : absOp o = .snap (absSnapMd o.idx o.term) := by simp [absOp, ho]
      simp only [tFoldChkFrom, ho, ite_true, List.map_cons, hop, walFoldChkFrom]
      exact ih _ _ (tSaveSnap_agree hs o.idx o.term)
    | false =>
      have hop : absOp o = .save (absHs o.hs) (o.ents.map absEnt) := by simp [absOp, ho]
      simp only [tFoldChkFrom, ho, Bool.false_eq_true, ite_false, List.map_cons, hop, walFoldChkFrom]
      have hR := tReadEnts_abs s.baseIdx o.ents s.ents
      rw [tAgree_b hs, tAgree_ents hs] at hR
      cases hx : o.ents.foldlM (fun ents e => tReadEnt s.baseIdx ents e) s.ents with
      | none =>
        rw [hx] at hR
        simp only [Option.map_none] at hR
        rw [← hR]; rfl
      | some x =>
        rw [hx] at hR
        simp only [Option.map_some] at hR
        rw [← hR]
        dsimp only [bind, Option.bind]
        apply ih
        unfold tAgree absC projC
        have hhs : absHs s.hs = σ.hs := by
          have := congrArg (fun x => x.1) hs; simpa [absC, projC] using this
        have hbi := congrArg (fun x => x.2.1) hs
        have hbt := congrArg (fun x => x.2.2.1) hs
        simp only [absC, projC] at hbi hbt
        simp only [absHs_phsNext, hhs, hbi, hbt]

/-! ## The reads -/

theorem tKeep_abs (c : w64) (o : TOp) : tKeep c o = walKeep (uint.nat c) (absOp o) := by
  unfold tKeep walKeep absOp
  cases o.snap <;> simp [absSnapMd, ← decide_not, Nat.not_le]

theorem filter_tKeep_abs (c : w64) (h : List TOp) :
    (h.filter (tKeep c)).map absOp = (h.map absOp).filter (walKeep (uint.nat c)) := by
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro o _
  simp [tKeep_abs]

theorem tC0_agree : tAgree tC0 walFresh := rfl

theorem tRead_abs (h : List TOp) : (tRead h).map absC = (walRead (h.map absOp)).map projC := by
  unfold tRead walRead tFoldChk
  rw [tLastHS_commit, ← filter_tKeep_abs]
  have hc : (walLastHS (h.map absOp)).Commit' = (tLastHS h).commit' := (tLastHS_commit h).symm
  rw [hc]
  exact tFoldChkFrom_abs _ _ _ tC0_agree

/-- The newest pair, step by step. -/
theorem tNewest_abs_gen : ∀ (f : List TOp) (acc : Option (w64 × w64)) (accm : Option SnapshotMetadataM),
    acc = accm.map (fun m => (m.Index', m.Term')) →
    f.foldl (fun acc o => if o.snap then
        (match acc with
          | none => some (o.idx, o.term)
          | some b => if uint.nat b.1 ≤ uint.nat o.idx then some (o.idx, o.term) else acc)
      else acc) acc =
    ((f.map absOp).foldl (fun best o => match o with
      | .snap m => match best with
        | none => some m
        | some b => if uint.nat b.Index' ≤ uint.nat m.Index' then some m else best
      | .save _ _ => best) accm).map (fun m => (m.Index', m.Term')) := by
  intro f
  induction f with
  | nil => intro acc accm h; exact h
  | cons o f ih =>
    intro acc accm h
    simp only [List.foldl_cons, List.map_cons]
    apply ih
    cases ho : o.snap with
    | true =>
      simp only [absOp, ho, ite_true]
      cases accm with
      | none => subst h; simp [absSnapMd]
      | some b =>
        subst h
        simp only [Option.map_some]
        by_cases hb : uint.nat b.Index' ≤ uint.nat o.idx
        · simp [hb, absSnapMd]
        · simp [hb, absSnapMd]
    | false => simp [absOp, ho, h]

theorem tNewest_abs (f : List TOp) :
    tNewest f = (walNewest (f.map absOp)).map (fun m => (m.Index', m.Term')) :=
  tNewest_abs_gen f none none rfl

theorem tReadFrom_abs (h : List TOp) (k : Nat) :
    (tReadFrom h k).map absC = (walReadFrom (h.map absOp) k).map projC := by
  unfold tReadFrom walReadFrom
  simp only
  rw [tLastHS_commit, ← List.map_drop]
  have hc : (walLastHS (h.map absOp)).Commit' = (tLastHS h).commit' := (tLastHS_commit h).symm
  rw [hc, ← filter_tKeep_abs, tNewest_abs]
  cases hn : walNewest (((h.drop k).filter (tKeep (tLastHS h).commit')).map absOp) with
  | none => rfl
  | some m =>
    simp only [Option.map_some]
    apply tFoldChkFrom_abs
    unfold tAgree absC projC
    simp only [List.map_nil, Prod.mk.injEq, and_true, true_and]
    rw [← List.map_take, ← tLastHS_abs]

/-- **The reads commute with the abstraction** (plan §2.5, item 2). -/
theorem tReadCut_abs (h : List TOp) (k : w64) :
    (tReadCut h k).map absC = (walReadCut (h.map absOp) (uint.nat k)).map projC := by
  unfold tReadCut walReadCut
  by_cases hk : k = W64 0
  · subst hk; simp only [ite_true]; exact tRead_abs h
  · have hk' : uint.nat k ≠ 0 := by intro h0; apply hk; word
    rw [if_neg hk, if_neg hk']
    exact tReadFrom_abs h _

/-! ## The images -/

theorem mem_tImgs {h : List TOp} {n j : Nat} {img : List TOp} (hn : n ≤ j) (hj : j ≤ h.length)
    (himg : img ∈ h.take j :: tTornImgs h j) : img ∈ tImgs h n := by
  unfold tImgs
  rw [List.mem_flatMap]
  exact ⟨j, by rw [List.mem_range'_1]; omega, himg⟩

theorem absOp_save {o : TOp} {hs : HardStateM} {es : List EntryM}
    (h : absOp o = .save hs es) : o.snap = false ∧ hs = absHs o.hs ∧ es = o.ents.map absEnt := by
  unfold absOp at h
  cases ho : o.snap
  · simp only [ho, Bool.false_eq_true, ite_false, WalOpG.save.injEq] at h
    exact ⟨rfl, h.1.symm, h.2.symm⟩
  · simp only [ho, ite_true] at h; cases h

theorem absHs_empty {h : THs} (he : tHsEmpty h = true) : absHs h = ⟨0, 0, 0⟩ := by
  have := (tHsEmpty_iff h).1 he
  obtain ⟨h1, h2, h3⟩ := this
  simp only [absHs] at h1 h2 h3
  simp only [absHs, h1, h2, h3]; rfl

/-- **`walImgs` enumerates the images** (plan §2.5, item 1): every image of the abstraction of `h` at
the mark `n` is the abstraction of an image `walImgs h n` lists. -/
theorem tImgs_complete {h : List TOp} {n : Nat} {I : WalHist} (hI : walImg (h.map absOp) n I) :
    ∃ img ∈ tImgs h n, I = img.map absOp := by
  obtain ⟨j, h1, h2, h3 | ⟨hs, es, k, hj, hk, h3⟩⟩ := hI
  · simp only [List.length_map] at h2
    exact ⟨h.take j, mem_tImgs h1 h2 (List.mem_cons_self ..), by rw [h3, List.map_take]⟩
  · rw [List.getElem?_map] at hj
    cases hoj : h[j]? with
    | none => rw [hoj] at hj; cases hj
    | some o =>
      rw [hoj] at hj
      simp only [Option.map_some, Option.some.injEq] at hj
      obtain ⟨hsn, hhs, hes⟩ := absOp_save hj
      have hjl : j < h.length := getElem?_some_lt hoj
      subst hes hhs
      simp only [List.length_map] at hk h2
      by_cases hlast : k = o.ents.length ∧ tHsEmpty o.hs = true
      · obtain ⟨rfl, he⟩ := hlast
        refine ⟨h.take (j + 1), mem_tImgs (by omega) hjl (List.mem_cons_self ..), ?_⟩
        rw [h3, List.map_take, List.take_succ, List.getElem?_map, hoj, Option.map_some, hj,
          absHs_empty he]
        rw [List.take_of_length_le (l := o.ents.map absEnt) (by simp)]
        rfl
      · refine ⟨h.take j ++ [tTornOp (o.ents.take k)], mem_tImgs h1 h2 (List.mem_cons_of_mem _ ?_), ?_⟩
        · unfold tTornImgs
          rw [hoj]
          simp only [hsn, Bool.false_eq_true, ite_false, List.mem_map, List.mem_range]
          refine ⟨k, ?_, rfl⟩
          split
          · rename_i he
            have : k ≠ o.ents.length := fun hk' => hlast ⟨hk', he⟩
            omega
          · omega
        · rw [h3, List.map_append, List.map_take]
          simp only [List.map_cons, List.map_nil, absOp, tTornOp, Bool.false_eq_true, ite_false,
            List.map_take]
          rfl

/-! ## `openBound` -/

theorem tOpenBound_fold_ge (a : w64) : ∀ (imgs : List (List TOp)) (acc : w64),
    uint.nat acc ≤ uint.nat (imgs.foldl (fun best i =>
      if uint.nat best < uint.nat (tNameBound i a) then tNameBound i a else best) acc) ∧
    ∀ i ∈ imgs, uint.nat (tNameBound i a) ≤ uint.nat (imgs.foldl (fun best i =>
      if uint.nat best < uint.nat (tNameBound i a) then tNameBound i a else best) acc) := by
  intro imgs
  induction imgs with
  | nil => intro acc; exact ⟨Nat.le_refl _, fun i hi => by cases hi⟩
  | cons x imgs ih =>
    intro acc
    simp only [List.foldl_cons]
    have h1 : uint.nat acc ≤ uint.nat (if uint.nat acc < uint.nat (tNameBound x a) then tNameBound x a else acc) ∧
        uint.nat (tNameBound x a) ≤
          uint.nat (if uint.nat acc < uint.nat (tNameBound x a) then tNameBound x a else acc) := by
      split <;> omega
    obtain ⟨ih1, ih2⟩ := ih (if uint.nat acc < uint.nat (tNameBound x a) then tNameBound x a else acc)
    refine ⟨Nat.le_trans h1.1 ih1, ?_⟩
    intro i hi
    rcases List.mem_cons.1 hi with rfl | hi
    · exact Nat.le_trans h1.2 ih1
    · exact ih2 i hi

/-- **`openBound` bounds each image's name bound** (an `Open` after a crash raises `unl` at most to
the name bound of the image it opened, one of them). -/
theorem tNameBound_le_openBound {imgs : List (List TOp)} {img : List TOp} (a : w64)
    (h : img ∈ imgs) : uint.nat (tNameBound img a) ≤ uint.nat (tOpenBound imgs a) :=
  (tOpenBound_fold_ge a imgs (W64 0)).2 img h

/-! ## The last index, cut positions and the name bound -/

theorem tLastEnt_abs : ∀ (l : List TOp) (x : w64),
    uint.nat (l.foldl (fun x o => if o.snap then x else (o.ents.getLast?.map (·.index')).getD x) x) =
      (l.map absOp).foldl walLastEntF (uint.nat x) := by
  intro l
  induction l with
  | nil => intro x; rfl
  | cons o l ih =>
    intro x
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    congr 1
    cases ho : o.snap
    · simp only [absOp, ho, Bool.false_eq_true, ite_false, walLastEntF, List.getLast?_map]
      cases o.ents.getLast? <;> rfl
    · simp [absOp, ho, walLastEntF]

theorem tMaxSnap_abs : ∀ (l : List TOp) (x : w64),
    uint.nat (l.foldl (fun x o => if o.snap ∧ uint.nat x < uint.nat o.idx then o.idx else x) x) =
      (l.map absOp).foldl walMaxSnapF (uint.nat x) := by
  intro l
  induction l with
  | nil => intro x; rfl
  | cons o l ih =>
    intro x
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    congr 1
    cases ho : o.snap
    · simp [absOp, ho, walMaxSnapF]
    · simp only [absOp, ho, ite_true, walMaxSnapF, absSnapMd, true_and]
      split <;> omega

/-- **`lastIdx` is `walLastIdx`** (no bound needed: no arithmetic). -/
theorem tLastIdx_abs (h : List TOp) : uint.nat (tLastIdx h) = walLastIdx (h.map absOp) := by
  rw [walLastIdx_eq]
  unfold tLastIdx
  simp only
  have h1 := tLastEnt_abs h (W64 0)
  have h2 := tMaxSnap_abs h (W64 0)
  simp only [show uint.nat (W64 0) = 0 from rfl] at h1 h2
  split
  · rename_i hc; rw [h1, h2] at hc; rw [h2]; exact (Nat.max_eq_right (Nat.le_of_lt hc)).symm
  · rename_i hc; rw [h1, h2] at hc; rw [h1]; exact (Nat.max_eq_left (Nat.le_of_not_lt hc)).symm

/-- **`cutPos` is `walCutPos`**. -/
theorem tCutPos_abs (h : List TOp) (b : Nat) : tCutPos h b = true ↔ walCutPos (h.map absOp) b := by
  unfold tCutPos walCutPos
  rw [List.getElem?_map]
  by_cases hb : b = 0
  · simp [hb]
  · simp only [hb, decide_false, Bool.false_or, false_or]
    cases hx : h[b - 1]? with
    | none => simp
    | some o =>
      simp only [Option.map_some, Option.some.injEq]
      cases ho : o.snap
      · simp only [absOp, ho, Bool.false_eq_true, ite_false, WalOpG.save.injEq, Bool.not_false,
          Bool.true_and, Bool.not_eq_true', Bool.and_eq_false_iff]
        constructor
        · intro hne
          refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩
          rintro ⟨he, hn⟩
          rcases hne with hne | hne
          · rw [(tHsEmpty_iff o.hs).2 he] at hne; cases hne
          · rw [List.map_eq_nil_iff] at hn; rw [hn] at hne; cases hne
        · rintro ⟨_, _, ⟨rfl, rfl⟩, hne⟩
          by_cases he : tHsEmpty o.hs = true
          · right
            cases hes : o.ents with
            | nil => exact absurd ⟨(tHsEmpty_iff o.hs).1 he, by simp [hes]⟩ hne
            | cons _ _ => rfl
          · left; simpa using he
      · simp [absOp, ho]

/-- Every index of a well-formed history is below `2^63`. -/
theorem tHistWf_take {h : List TOp} (hw : tHistWf h) (b : Nat) : tHistWf (h.take b) :=
  fun o ho => hw o (List.mem_of_mem_take ho)

theorem tLastEnt_lt : ∀ (l : List TOp) (x : w64), tHistWf l → uint.nat x < 2 ^ 63 →
    uint.nat (l.foldl (fun x o => if o.snap then x else (o.ents.getLast?.map (·.index')).getD x) x) <
      2 ^ 63 := by
  intro l
  induction l with
  | nil => intro x _ hx; exact hx
  | cons o l ih =>
    intro x hw hx
    simp only [List.foldl_cons]
    apply ih _ (fun o' ho' => hw o' (List.mem_cons_of_mem _ ho'))
    cases ho : o.snap
    · simp only [Bool.false_eq_true, ite_false]
      cases hl : o.ents.getLast? with
      | none => exact hx
      | some e =>
        exact ((hw o (List.mem_cons_self ..)).2 ho e (List.mem_of_getLast? hl)).2.2.1
    · simpa using hx

theorem tMaxSnap_lt : ∀ (l : List TOp) (x : w64), tHistWf l → uint.nat x < 2 ^ 63 →
    uint.nat (l.foldl (fun x o => if o.snap ∧ uint.nat x < uint.nat o.idx then o.idx else x) x) <
      2 ^ 63 := by
  intro l
  induction l with
  | nil => intro x _ hx; exact hx
  | cons o l ih =>
    intro x hw hx
    simp only [List.foldl_cons]
    apply ih _ (fun o' ho' => hw o' (List.mem_cons_of_mem _ ho'))
    split
    · rename_i hc; exact ((hw o (List.mem_cons_self ..)).1 hc.1).1
    · exact hx

/-- The last index of a well-formed history is below `2^63`. -/
theorem tLastIdx_lt {h : List TOp} (hw : tHistWf h) : uint.nat (tLastIdx h) < 2 ^ 63 := by
  have h1 := tLastEnt_lt h (W64 0) hw (by decide)
  have h2 := tMaxSnap_lt h (W64 0) hw (by decide)
  unfold tLastIdx
  simp only
  split <;> assumption

/-- A well-formed history has no index `2^64-1`. -/
theorem tHistWf_noMax {h : List TOp} (hw : tHistWf h) : ¬ walHasMaxIdx (h.map absOp) := by
  rintro ⟨o', ho', hm⟩
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 ho'
  have hwo := hw o ho
  cases hs : o.snap
  · simp only [absOp, hs, Bool.false_eq_true, ite_false] at hm
    obtain ⟨e', he', hi⟩ := hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
    have := (hwo.2 hs e he).2.2.1
    simp only [absEnt] at hi; omega
  · simp only [absOp, hs, ite_true, absSnapMd] at hm
    have := (hwo.1 hs).1; omega

open Classical in
/-- **`nameBound` is `walNameBound … false`** for a well-formed history (no index wraps, so
`lastIdx + 1` does not) of fewer than `2^64` operations (the bound fits a `uint64`). -/
theorem tNameBound_eq {h : List TOp} (hw : tHistWf h) (hl : h.length < 2 ^ 64) (a : w64) :
    uint.nat (tNameBound h a) = walNameBound (h.map absOp) (uint.nat a) false := by
  unfold tNameBound walNameBound
  rw [if_neg (tHistWf_noMax hw)]
  simp only [List.length_map, Bool.false_eq_true, ite_false]
  have hfil : (List.range (h.length + 1)).filter (fun b =>
      tCutPos h b && decide (uint.nat (tLastIdx (h.take b) + W64 1) ≤ uint.nat a)) =
      (List.range (h.length + 1)).filter (fun b => decide (walCutPos (h.map absOp) b ∧
        walLastIdx ((h.map absOp).take b) + 1 ≤ uint.nat a)) := by
    apply List.filter_congr
    intro b _
    have hlt := tLastIdx_lt (tHistWf_take hw b)
    have hadd : uint.nat (tLastIdx (h.take b) + W64 1) = uint.nat (tLastIdx (h.take b)) + 1 := by
      word
    rw [hadd, tLastIdx_abs, ← List.map_take]
    by_cases hc : walCutPos (h.map absOp) b
    · simp [(tCutPos_abs h b).2 hc, hc]
    · have : tCutPos h b = false := by
        cases hh : tCutPos h b
        · rfl
        · exact absurd ((tCutPos_abs h b).1 hh) hc
      simp [this, hc]
  rw [hfil]
  have hmem : ∀ x ∈ ((List.range (h.length + 1)).filter (fun b => decide (walCutPos (h.map absOp) b ∧
        walLastIdx ((h.map absOp).take b) + 1 ≤ uint.nat a))).getLast?, x ≤ h.length := by
    intro x hx
    have := List.mem_of_getLast? hx
    rw [List.mem_filter, List.mem_range] at this
    omega
  cases hg : ((List.range (h.length + 1)).filter (fun b => decide (walCutPos (h.map absOp) b ∧
        walLastIdx ((h.map absOp).take b) + 1 ≤ uint.nat a))).getLast? with
  | none => rfl
  | some x =>
    have := hmem x (by rw [hg]; rfl)
    simp only [Option.getD_some]
    word

end pure

end etcd_wal
end EtcdGrove
end Perennial
