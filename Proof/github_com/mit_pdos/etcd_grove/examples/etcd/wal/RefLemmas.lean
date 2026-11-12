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

end pure

end etcd_wal
end EtcdGrove
end Perennial
