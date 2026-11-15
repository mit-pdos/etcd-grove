/-
Lean-first (no Rocq counterpart).

# Two folds of one history, one applying more snapshot records (W4c U5, tenth session)

The pure core of `tReadsBackOk`'s invariant (`TP/ReadsBack.lean`). A restart's read (`walRead`) folds
the history's records with every snapshot record at or below the last commit applied. The tester's
member, though, has a view of the log that ignores some records: a received snapshot's record whose
`Save` a crash lost and a restart then read past (the record stays in the WAL above the commit, and
becomes applicable once the commit passes it). This file compares two folds of one history:

* the **guide** `G`, which applies only the records the list marks `true` (`gFold`, checking at every
  step that its commit is at most its last index, and that every snapshot record, applied or not,
  satisfies `gSnapOk`: below the base, at or below the commit, or at or above the last index);
* any fold `R` that applies **at least** the guide's records (`remask c`: every record at or below `c`).

`gFold_remask`: when the guide succeeds and `R` starts related to it (`SRel`: same hard state, a base at
least the guide's, the guide's entries above it), `R` succeeds too, related at the end, and passes the
same checks. `gFold_readsBack`: a guide that marks exactly the records at or below the history's last
commit is `walRead`'s fold, so the history reads back (`walReadsBack`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.WalReadAllPost

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open go_etcd_io.raft.v3 WalEnc

section pure
variable [GooseExts]

/-- **A snapshot record's admissibility against the guide's state**: below its base (no effect), at
or below its commit (an applied snapshot), or at or above its last index (a received one). -/
def gSnapOk (m : SnapshotMetadataM) (G : StorContents) : Bool :=
  decide (uint.nat m.Index' < G.b ∨ uint.nat m.Index' ≤ G.commit ∨ G.last ≤ uint.nat m.Index')

/-- **The guide's step**: a `Save` (always applied, then commit at most last index), a snapshot
record (admissible; applied iff marked). -/
def gStep (G : StorContents) : WalOp × Bool → Option StorContents
  | (.save h es, true) => match walFoldChkFrom G [.save h es] with
      | some G' => if G'.commit ≤ G'.last then some G' else none
      | none => none
  | (.save _ _, false) => none
  | (.snap m, b) => if gSnapOk m G then some (if b then walSaveSnap G m else G) else none

/-- **The guide's fold.** -/
def gFold (G : StorContents) : List (WalOp × Bool) → Option StorContents
  | [] => some G
  | x :: L => (gStep G x).bind (fun G' => gFold G' L)

theorem gFold_append (G : StorContents) (A B : List (WalOp × Bool)) :
    gFold G (A ++ B) = (gFold G A).bind (fun G1 => gFold G1 B) := by
  induction A generalizing G with
  | nil => rfl
  | cons x A ih =>
    simp only [List.cons_append, gFold]
    cases gStep G x with
    | none => rfl
    | some G' => exact ih G'

/-- Mark the records at or below `c` (and every `Save`). -/
def remask (c : Nat) (L : List (WalOp × Bool)) : List (WalOp × Bool) :=
  L.map (fun x => (x.1, walKeep c x.1))

theorem remask_append (c : Nat) (A B : List (WalOp × Bool)) :
    remask c (A ++ B) = remask c A ++ remask c B := List.map_append

theorem remask_fst (c : Nat) (L : List (WalOp × Bool)) : (remask c L).map Prod.fst = L.map Prod.fst := by
  simp [remask, Function.comp_def]

/-- **`R` is related to the guide `G`**: same hard state, a base at least the guide's, the guide's
entries above it. -/
def SRel (R G : StorContents) : Prop :=
  R.hs = G.hs ∧ G.b ≤ R.b ∧ R.ents = G.ents.drop (R.b - G.b)

theorem SRel_refl (G : StorContents) : SRel G G := ⟨rfl, Nat.le_refl _, by simp⟩

theorem SRel_last {R G : StorContents} (h : SRel R G) : R.last = max R.b G.last := by
  obtain ⟨-, hb, he⟩ := h
  simp only [StorContents.last, he, List.length_drop]
  omega

theorem SRel_commit {R G : StorContents} (h : SRel R G) : R.commit = G.commit := by
  simp only [StorContents.commit, h.1]

/-! ## `Save`: the entries -/

theorem drop_take_snoc {α : Type} (l : List α) (x : α) (n k : Nat) (hk : k ≤ n) (hn : n ≤ l.length) :
    (l.take n ++ [x]).drop k = (l.drop k).take (n - k) ++ [x] := by
  rw [List.drop_append_of_le_length (by simp; omega), List.drop_take]

theorem readEnt_rel {b b' : Nat} (hb : b ≤ b') {g g' : List EntryM} {e : EntryM}
    (h : readEnt b g e = some g') : ∃ r', readEnt b' (g.drop (b' - b)) e = some r' ∧
      r' = g'.drop (b' - b) := by
  unfold readEnt at h ⊢
  by_cases h1 : uint.nat e.Index' ≤ b
  · rw [if_pos h1] at h; cases h
    exact ⟨[], by rw [if_pos (by omega)], by simp⟩
  · rw [if_neg h1] at h
    by_cases h2 : uint.nat e.Index' - b - 1 ≤ g.length
    · rw [if_pos h2] at h; cases h
      by_cases h3 : uint.nat e.Index' ≤ b'
      · refine ⟨[], by rw [if_pos h3], ?_⟩
        symm; apply List.drop_eq_nil_of_le; simp; omega
      · rw [if_neg h3, if_pos (by simp; omega)]
        refine ⟨_, rfl, ?_⟩
        rw [drop_take_snoc _ _ _ _ (by omega) h2]
        congr 2; omega
    · rw [if_neg h2] at h; cases h

theorem readEnts_rel {b b' : Nat} (hb : b ≤ b') : ∀ (es : List EntryM) {g g' : List EntryM},
    es.foldlM (fun ents e => readEnt b ents e) g = some g' →
    es.foldlM (fun ents e => readEnt b' ents e) (g.drop (b' - b)) = some (g'.drop (b' - b)) := by
  intro es
  induction es with
  | nil =>
    intro g g' h
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h ⊢; rw [h]
  | cons e es ih =>
    intro g g' h
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨y, hy, h⟩ := h
    obtain ⟨r', hr, rfl⟩ := readEnt_rel hb hy
    exact ⟨_, hr, ih h⟩

theorem walFoldChkFrom_save1 (σ : StorContents) (h : HardStateM) (es : List EntryM) :
    walFoldChkFrom σ [.save h es] = (es.foldlM (fun ents e => readEnt σ.b ents e) σ.ents).map
      (fun ents => { σ with hs := phsNext σ.hs h, ents := ents }) := by
  simp only [walFoldChkFrom, Option.bind_eq_bind]
  cases es.foldlM (fun ents e => readEnt σ.b ents e) σ.ents <;> rfl

theorem save_rel {R G G' : StorContents} (hr : SRel R G) (h : HardStateM) (es : List EntryM)
    (hg : walFoldChkFrom G [.save h es] = some G') :
    ∃ R', walFoldChkFrom R [.save h es] = some R' ∧ SRel R' G' := by
  obtain ⟨h1, h2, h3⟩ := hr
  rw [walFoldChkFrom_save1] at hg ⊢
  obtain ⟨g', hg', rfl⟩ := Option.map_eq_some_iff.1 hg
  rw [h3, readEnts_rel h2 es hg']
  refine ⟨_, rfl, ?_, h2, rfl⟩
  simp only [h1]

/-! ## Snapshot records -/

theorem walSaveSnap_noop {σ : StorContents} {m : SnapshotMetadataM} (h : uint.nat m.Index' < σ.b) :
    walSaveSnap σ m = σ := by
  unfold walSaveSnap; rw [if_pos h]

theorem walSaveSnap_b {σ : StorContents} {m : SnapshotMetadataM} (h : ¬ uint.nat m.Index' < σ.b) :
    (walSaveSnap σ m).b = uint.nat m.Index' := by
  unfold walSaveSnap; rw [if_neg h]; rfl

theorem walSaveSnap_ents {σ : StorContents} {m : SnapshotMetadataM} (h : ¬ uint.nat m.Index' < σ.b) :
    (walSaveSnap σ m).ents =
      if uint.nat m.Index' ≤ σ.commit then σ.ents.drop (uint.nat m.Index' - σ.b) else [] := by
  unfold walSaveSnap; rw [if_neg h]

/-- Both apply the record. -/
theorem snap_rel_both {R G : StorContents} (hr : SRel R G) {m : SnapshotMetadataM}
    (hok : gSnapOk m G = true) : SRel (walSaveSnap R m) (walSaveSnap G m) := by
  have hc := SRel_commit hr
  obtain ⟨h1, h2, h3⟩ := hr
  simp only [gSnapOk, decide_eq_true_eq] at hok
  have hl : G.last = G.b + G.ents.length := rfl
  by_cases hg : uint.nat m.Index' < G.b
  · rw [walSaveSnap_noop hg, walSaveSnap_noop (by omega)]; exact ⟨h1, h2, h3⟩
  · refine ⟨by rw [walSaveSnap_hs, walSaveSnap_hs, h1], ?_, ?_⟩
    · rw [walSaveSnap_b hg]
      by_cases hR : uint.nat m.Index' < R.b
      · rw [walSaveSnap_noop hR]; omega
      · rw [walSaveSnap_b hR]; exact Nat.le_refl _
    · rw [walSaveSnap_b hg, walSaveSnap_ents hg]
      by_cases hR : uint.nat m.Index' < R.b
      · rw [walSaveSnap_noop hR, h3]
        split
        · rw [List.drop_drop]; congr 1; omega
        · next hgc =>
          rw [List.drop_nil]; apply List.drop_eq_nil_of_le; omega
      · rw [walSaveSnap_b hR, walSaveSnap_ents hR, hc, h3]
        split
        · rw [List.drop_drop, Nat.sub_self, List.drop_zero]; congr 1; omega
        · simp

/-- Only `R` applies the record. -/
theorem snap_rel_right {R G : StorContents} (hr : SRel R G) {m : SnapshotMetadataM}
    (hok : gSnapOk m G = true) : SRel (walSaveSnap R m) G := by
  have hc := SRel_commit hr
  obtain ⟨h1, h2, h3⟩ := hr
  simp only [gSnapOk, decide_eq_true_eq] at hok
  have hl : G.last = G.b + G.ents.length := rfl
  by_cases hR : uint.nat m.Index' < R.b
  · rw [walSaveSnap_noop hR]; exact ⟨h1, h2, h3⟩
  · refine ⟨by rw [walSaveSnap_hs, h1], by rw [walSaveSnap_b hR]; omega, ?_⟩
    rw [walSaveSnap_b hR, walSaveSnap_ents hR, hc, h3]
    split
    · rw [List.drop_drop]; congr 1; omega
    · next hgc =>
      symm; apply List.drop_eq_nil_of_le; omega

/-- The admissibility carries over to a related `R`. -/
theorem gSnapOk_rel {R G : StorContents} (hr : SRel R G) {m : SnapshotMetadataM}
    (hok : gSnapOk m G = true) : gSnapOk m R = true := by
  have hc := SRel_commit hr
  have hl := SRel_last hr
  have h2 := hr.2.1
  simp only [gSnapOk, decide_eq_true_eq] at hok ⊢
  omega

/-! ## The guide's fold, re-marked -/

/-- **A fold applying at least the guide's records follows it** (`R` related at every step). -/
theorem gFold_remask (c : Nat) : ∀ (L : List (WalOp × Bool)) {R G G1 : StorContents},
    gFold G L = some G1 → SRel R G →
    (∀ m, (WalOpG.snap m, true) ∈ L → uint.nat m.Index' ≤ c) →
    ∃ R1, gFold R (remask c L) = some R1 ∧ SRel R1 G1 := by
  intro L
  induction L with
  | nil => intro R G G1 h hr _; cases h; exact ⟨R, rfl, hr⟩
  | cons x L ih =>
    intro R G G1 h hr hk
    obtain ⟨o, b⟩ := x
    simp only [gFold, Option.bind_eq_some_iff] at h
    obtain ⟨G', hst, h⟩ := h
    have hk' : ∀ m, (WalOpG.snap m, true) ∈ L → uint.nat m.Index' ≤ c :=
      fun m hm => hk m (List.mem_cons_of_mem _ hm)
    cases o with
    | save hs es =>
      cases b with
      | false => cases hst
      | true =>
        simp only [gStep] at hst
        split at hst
        · next G2 hg2 =>
          split at hst
          · next hcl =>
            cases hst
            obtain ⟨R', hR', hrel⟩ := save_rel hr hs es hg2
            obtain ⟨R1, hR1, hrel1⟩ := ih h hrel hk'
            refine ⟨R1, ?_, hrel1⟩
            simp only [remask, List.map_cons, walKeep, gFold, gStep, hR'] at hR1 ⊢
            have : R'.commit ≤ R'.last := by
              rw [SRel_commit hrel, SRel_last hrel]; omega
            rw [if_pos this]; exact hR1
          · cases hst
        · cases hst
    | snap m =>
      simp only [gStep] at hst
      split at hst
      · next hok =>
        cases hst
        have hokR := gSnapOk_rel hr hok
        have hrel : SRel (if walKeep c (WalOpG.snap m) then walSaveSnap R m else R)
            (if b then walSaveSnap G m else G) := by
          cases b with
          | true =>
            have hkm : walKeep c (WalOpG.snap m) = true := by
              simp only [walKeep, decide_eq_true_eq]; exact hk m (List.mem_cons_self ..)
            rw [if_pos hkm]; exact snap_rel_both hr hok
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            split
            · exact snap_rel_right hr hok
            · exact hr
        obtain ⟨R1, hR1, hrel1⟩ := ih h hrel hk'
        refine ⟨R1, ?_, hrel1⟩
        simp only [remask, List.map_cons, gFold, gStep, hokR, ↓reduceIte, Option.bind_some] at hR1 ⊢
        exact hR1
      · cases hst

/-! ## A guide of the restart's own marks reads back -/

theorem gStep_commitLe {G G' : StorContents} {x : WalOp × Bool} (hG : G.commit ≤ G.last)
    (h : gStep G x = some G') : G'.commit ≤ G'.last := by
  obtain ⟨o, b⟩ := x
  cases o with
  | save hs es =>
    cases b with
    | false => cases h
    | true =>
      simp only [gStep] at h
      split at h
      · split at h
        · cases h; assumption
        · cases h
      · cases h
  | snap m =>
    simp only [gStep] at h
    split at h
    · cases h; split
      · exact walSaveSnap_commitLe m hG
      · exact hG
    · cases h

theorem gFold_commitLe : ∀ (L : List (WalOp × Bool)) {G G1 : StorContents}, G.commit ≤ G.last →
    gFold G L = some G1 → G1.commit ≤ G1.last := by
  intro L
  induction L with
  | nil => intro G G1 hG h; cases h; exact hG
  | cons x L ih =>
    intro G G1 hG h
    simp only [gFold, Option.bind_eq_some_iff] at h
    obtain ⟨G', h1, h2⟩ := h
    exact ih (gStep_commitLe hG h1) h2

/-- **The re-marked guide is the filtered fold**, with the commit at most the last index along it. -/
theorem gFold_remask_filter (c : Nat) : ∀ (L : WalHist) {G G1 : StorContents}, G.commit ≤ G.last →
    gFold G (remask c (L.map (fun o => (o, true)))) = some G1 →
    walFoldChkFrom G (L.filter (walKeep c)) = some G1 ∧ walCommitLeFrom G (L.filter (walKeep c)) := by
  intro L
  induction L with
  | nil =>
    intro G G1 hG h; cases h
    refine ⟨rfl, ?_⟩
    intro n τ h; simp only [List.filter_nil, List.take_nil, walFoldChkFrom, Option.some.injEq] at h
    subst h; exact hG
  | cons o L ih =>
    intro G G1 hG h
    simp only [remask, List.map_cons, List.map_map] at h ih
    simp only [gFold, Option.bind_eq_some_iff] at h
    obtain ⟨G', hst, h⟩ := h
    have hG' := gStep_commitLe hG hst
    obtain ⟨ih1, ih2⟩ := ih hG' h
    cases o with
    | save hs es =>
      simp only [walKeep, gStep] at hst
      split at hst
      · next G2 hg2 =>
        split at hst
        · cases hst
          have hf : (WalOpG.save hs es :: L).filter (walKeep c) = WalOpG.save hs es :: L.filter (walKeep c) := by
            simp [List.filter_cons, walKeep]
          rw [hf]
          have happ : ∀ X : WalHist, walFoldChkFrom G (WalOpG.save hs es :: X) =
              (walFoldChkFrom G [WalOpG.save hs es]).bind (fun τ => walFoldChkFrom τ X) := fun X => by
            rw [show WalOpG.save hs es :: X = [WalOpG.save hs es] ++ X from rfl, walFoldChkFrom_append]
          refine ⟨by rw [happ, hg2]; exact ih1, ?_⟩
          intro n τ hτ
          cases n with
          | zero => simp only [List.take_zero, walFoldChkFrom, Option.some.injEq] at hτ; subst hτ; exact hG
          | succ n =>
            rw [List.take_succ_cons, happ, hg2, Option.bind_some] at hτ
            exact ih2 n τ hτ
        · cases hst
      · cases hst
    | snap m =>
      simp only [gStep] at hst
      split at hst
      · cases hst
        by_cases hk : walKeep c (WalOpG.snap m) = true
        · rw [if_pos hk] at ih1 ih2 hG'
          have hf : (WalOpG.snap m :: L).filter (walKeep c) = WalOpG.snap m :: L.filter (walKeep c) := by
            simp [List.filter_cons, hk]
          rw [hf]
          refine ⟨ih1, ?_⟩
          intro n τ hτ
          cases n with
          | zero => simp only [List.take_zero, walFoldChkFrom, Option.some.injEq] at hτ; subst hτ; exact hG
          | succ n =>
            rw [List.take_succ_cons] at hτ; simp only [walFoldChkFrom] at hτ
            exact ih2 n τ hτ
        · rw [if_neg hk] at ih1 ih2
          have hf : (WalOpG.snap m :: L).filter (walKeep c) = L.filter (walKeep c) := by
            simp [List.filter_cons, Bool.not_eq_true _ ▸ hk]
          rw [hf]; exact ⟨ih1, ih2⟩
      · cases hst

/-- **A history whose re-marked guide succeeds from the start reads back.** -/
theorem gFold_readsBack {I : WalHist} {σ : StorContents}
    (h : gFold walFresh (remask (uint.nat (walLastHS I).Commit') (I.map (fun o => (o, true)))) = some σ) :
    walReadsBack I ∧ walRead I = some σ := by
  obtain ⟨h1, h2⟩ := gFold_remask_filter _ I (by simp [walFresh, StorContents.commit, StorContents.last]) h
  exact ⟨⟨h2, σ, h1⟩, h1⟩

/-! ## A received snapshot's torn `Save`: `ReadAll` fails -/

theorem gFold_split (G : StorContents) (L : List (WalOp × Bool)) (k : Nat) {G1 : StorContents}
    (h : gFold G L = some G1) : ∃ Gk, gFold G (L.take k) = some Gk ∧ gFold Gk (L.drop k) = some G1 := by
  rw [← List.take_append_drop k L, gFold_append] at h
  cases hk : gFold G (L.take k) with
  | none => rw [hk] at h; cases h
  | some Gk => rw [hk, Option.bind_some] at h; exact ⟨Gk, rfl, h⟩

theorem readEnt_last_ge {b : Nat} {ents x : List EntryM} {e : EntryM} (h : readEnt b ents e = some x) :
    uint.nat e.Index' ≤ b + x.length := by
  unfold readEnt at h
  split at h
  · cases h; simp only [List.length_nil]; omega
  · split at h
    · cases h; simp only [List.length_append, List.length_take, List.length_singleton]; omega
    · cases h

theorem readEnts_last_ge {b : Nat} : ∀ {es : List EntryM} {ents x : List EntryM} {e : EntryM},
    es.foldlM (fun ents e => readEnt b ents e) ents = some x → es.getLast? = some e →
    uint.nat e.Index' ≤ b + x.length := by
  intro es
  induction es with
  | nil => intro ents x e _ h; cases h
  | cons e0 es ih =>
    intro ents x e h hl
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨y, hy, h⟩ := h
    cases es with
    | nil =>
      simp only [List.getLast?_singleton, Option.some.injEq] at hl; subst hl
      simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h; subst h
      exact readEnt_last_ge hy
    | cons e1 es => exact ih h (by rw [List.getLast?_cons_cons] at hl; exact hl)

/-- The guide's last index does not go down at a snapshot record. -/
theorem gSnap_last_ge {G : StorContents} {m : SnapshotMetadataM} (hok : gSnapOk m G = true) (b : Bool) :
    G.last ≤ (if b then walSaveSnap G m else G).last := by
  cases b with
  | false => exact Nat.le_refl _
  | true =>
    simp only [↓reduceIte]
    simp only [gSnapOk, decide_eq_true_eq] at hok
    by_cases hg : uint.nat m.Index' < G.b
    · rw [walSaveSnap_noop hg]; exact Nat.le_refl _
    · have hb := walSaveSnap_b hg
      have he := walSaveSnap_ents hg
      simp only [StorContents.last, hb, he]
      simp only [StorContents.last] at hok
      split
      · simp only [List.length_drop]; omega
      · simp only [List.length_nil]; omega

/-- **A fold at a fixed base `B` stays within the guide's last index** (or `B`). -/
theorem fold_bound (c B : Nat) : ∀ (L : List (WalOp × Bool)) {G G' τ0 τ : StorContents},
    gFold G L = some G' → τ0.b = B → τ0.last ≤ max B G.last →
    (∀ m, WalOpG.snap m ∈ L.map Prod.fst → uint.nat m.Index' ≤ c → uint.nat m.Index' ≤ B) →
    walFoldChkFrom τ0 ((L.map Prod.fst).filter (walKeep c)) = some τ →
    τ.b = B ∧ τ.last ≤ max B G'.last := by
  intro L
  induction L with
  | nil =>
    intro G G' τ0 τ h hb hl _ hf
    cases h; simp only [List.map_nil, List.filter_nil, walFoldChkFrom, Option.some.injEq] at hf
    subst hf; exact ⟨hb, hl⟩
  | cons x L ih =>
    intro G G' τ0 τ h hb hl hsn hf
    obtain ⟨o, bm⟩ := x
    simp only [gFold, Option.bind_eq_some_iff] at h
    obtain ⟨G2, hst, h⟩ := h
    have hsn' : ∀ m, WalOpG.snap m ∈ L.map Prod.fst → uint.nat m.Index' ≤ c → uint.nat m.Index' ≤ B :=
      fun m hm => hsn m (by simp only [List.map_cons]; exact List.mem_cons_of_mem _ hm)
    cases o with
    | save hs es =>
      cases bm with
      | false => cases hst
      | true =>
        simp only [gStep] at hst
        split at hst
        · next G3 hg3 =>
          split at hst
          · cases hst
            simp only [List.map_cons, List.filter_cons, walKeep, ↓reduceIte] at hf
            rw [show WalOpG.save hs es :: (L.map Prod.fst).filter (walKeep c) =
              [WalOpG.save hs es] ++ (L.map Prod.fst).filter (walKeep c) from rfl,
              walFoldChkFrom_append, walFoldChkFrom_save1] at hf
            rw [walFoldChkFrom_save1] at hg3
            cases hx : es.foldlM (fun ents e => readEnt τ0.b ents e) τ0.ents with
            | none => rw [hx] at hf; cases hf
            | some x =>
              rw [hx] at hf
              simp only [Option.map_some, Option.bind_some] at hf
              obtain ⟨gx, hgx, rfl⟩ := Option.map_eq_some_iff.1 hg3
              refine ih (τ0 := { τ0 with hs := phsNext τ0.hs hs, ents := x }) h hb ?_ hsn' hf
              simp only [StorContents.last, StorContents.b] at hl hb ⊢
              rcases readEnts_last hx with ⟨rfl, rfl⟩ | ⟨e, hle, hbd⟩
              · simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at hgx
                subst hgx; exact hl
              · have hge := readEnts_last_ge hgx hle
                simp only [StorContents.b] at hge hbd
                omega
          · cases hst
        · cases hst
    | snap m =>
      simp only [gStep] at hst
      split at hst
      · next hok =>
        cases hst
        have hlG := gSnap_last_ge hok bm
        simp only [List.map_cons, List.filter_cons] at hf
        by_cases hk : walKeep c (WalOpG.snap m) = true
        · rw [if_pos hk] at hf; simp only [walFoldChkFrom] at hf
          have hmB : uint.nat m.Index' ≤ B :=
            hsn m (by simp) (by simpa [walKeep] using hk)
          by_cases hlt : uint.nat m.Index' < τ0.b
          · rw [walSaveSnap_noop hlt] at hf
            exact ih h hb (by omega) hsn' hf
          · have hb' := walSaveSnap_b hlt
            have he' := walSaveSnap_ents hlt
            refine ih h (by rw [hb']; omega) ?_ hsn' hf
            simp only [StorContents.last, hb', he'] at hl ⊢
            simp only [StorContents.last] at hlG
            split
            · simp only [List.length_drop]; omega
            · simp only [List.length_nil]; omega
        · rw [if_neg hk] at hf
          exact ih h hb (by omega) hsn' hf
      · cases hst

theorem walLastHS_bad (P : WalHist) (m : SnapshotMetadataM) (es : List EntryM) :
    walLastHS (P ++ [WalOpG.snap m, WalOpG.save ⟨W64 0, W64 0, W64 0⟩ es]) = walLastHS P := by
  rw [walLastHS_eq, walLastHS_eq, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, walHsStep]
  exact phsNext_empty _ _ ⟨rfl, rfl, rfl⟩

theorem gFold_hs : ∀ (L : List (WalOp × Bool)) {G G1 : StorContents}, gFold G L = some G1 →
    G1.hs = (L.map Prod.fst).foldl walHsStep G.hs := by
  intro L
  induction L with
  | nil => intro G G1 h; cases h; rfl
  | cons x L ih =>
    intro G G1 h
    obtain ⟨o, b⟩ := x
    simp only [gFold, Option.bind_eq_some_iff] at h
    obtain ⟨G2, hst, h⟩ := h
    rw [ih h]
    simp only [List.map_cons, List.foldl_cons]
    congr 1
    cases o with
    | save hs es =>
      cases b with
      | false => cases hst
      | true =>
        simp only [gStep] at hst
        split at hst
        · next G3 hg3 =>
          split at hst
          · cases hst; rw [walFoldChkFrom_hs hg3]; rfl
          · cases hst
        · cases hst
    | snap m =>
      simp only [gStep] at hst
      split at hst
      · cases hst; split
        · rw [walSaveSnap_hs]; rfl
        · rfl
      · cases hst

theorem save_fail {τ : StorContents} {m : SnapshotMetadataM} (hl : τ.last < uint.nat m.Index')
    (h : HardStateM) {es : List EntryM} (hne : es ≠ [])
    (hes : ∀ e ∈ es, uint.nat m.Index' < uint.nat e.Index') : walFoldChkFrom τ [.save h es] = none := by
  rw [walFoldChkFrom_save1]
  cases es with
  | nil => exact absurd rfl hne
  | cons e es =>
    have he := hes e (List.mem_cons_self ..)
    have hr : readEnt τ.b τ.ents e = none := by
      simp only [StorContents.last] at hl
      unfold readEnt
      rw [if_neg (by omega), if_neg (by omega)]
    simp [List.foldlM_cons, hr]

/-- **The torn `Save` after a received snapshot's record fails `ReadAll`**: the history `P` (a guide
from the start, ending at `σ1`), the record `m` above both its commit and its last index, then the
`Save`'s first entries (above `m`) without its state record. From any position, `ReadAll`'s fold reaches
the entries with its last index below `m`'s (`fold_bound`), so the first of them is past the end. -/
theorem readAll_bad {L : List (WalOp × Bool)} {σ1 : StorContents} (hL : gFold walFresh L = some σ1)
    {m : SnapshotMetadataM} (hc : σ1.commit < uint.nat m.Index') (hl : σ1.last < uint.nat m.Index')
    {es : List EntryM} (hne : es ≠ []) (hes : ∀ e ∈ es, uint.nat m.Index' < uint.nat e.Index')
    (cut : Nat) (s : w64 × w64) (σ' : StorContents) :
    ¬ walReadAllOk (L.map Prod.fst ++ [WalOpG.snap m, WalOpG.save ⟨W64 0, W64 0, W64 0⟩ es]) cut s σ' := by
  rintro ⟨k, -, -, hs, hat⟩
  have hhs : walLastHS (L.map Prod.fst ++ [WalOpG.snap m, WalOpG.save ⟨W64 0, W64 0, W64 0⟩ es]) =
      σ1.hs := by
    rw [walLastHS_bad, walLastHS_eq, gFold_hs L hL]; rfl
  have hcI : uint.nat (walLastHS (L.map Prod.fst ++
      [WalOpG.snap m, WalOpG.save ⟨W64 0, W64 0, W64 0⟩ es])).Commit' = σ1.commit := by rw [hhs]; rfl
  obtain ⟨hsc, hsmax⟩ := validSnaps_bounds hs
  rw [hcI] at hsc hsmax
  unfold walReadAt at hat
  rw [hcI] at hat
  have hst : (⟨walLastHS ((L.map Prod.fst ++ [WalOpG.snap m, WalOpG.save ⟨W64 0, W64 0, W64 0⟩ es]).take k),
      none, entryID.mk s.2 s.1, []⟩ : StorContents).last = uint.nat s.1 := by
    simp only [StorContents.last, StorContents.b, List.length_nil, Nat.add_zero]
  have hlen : (L.map Prod.fst).length = L.length := List.length_map _
  by_cases hk : k ≤ L.length
  · obtain ⟨Gk, hGk, hGd⟩ := gFold_split walFresh L k hL
    have hdrop : (L.map Prod.fst ++ [WalOpG.snap m, WalOpG.save ⟨W64 0, W64 0, W64 0⟩ es]).drop k =
        (L.drop k).map Prod.fst ++ [WalOpG.snap m, WalOpG.save ⟨W64 0, W64 0, W64 0⟩ es] := by
      rw [List.drop_append_of_le_length (by rw [hlen]; exact hk), List.map_drop]
    rw [hdrop, List.filter_append, walFoldChkFrom_append] at hat
    have hnc : ¬ uint.nat m.Index' ≤ σ1.commit := by omega
    simp only [List.filter_cons, walKeep, hnc, decide_false, Bool.false_eq_true, ↓reduceIte, decide_true,
      List.filter_nil] at hat
    cases hX : walFoldChkFrom _ (((L.drop k).map Prod.fst).filter (walKeep σ1.commit)) with
    | none => rw [hX] at hat; cases hat
    | some τ =>
      rw [hX, Option.bind_some] at hat
      obtain ⟨hτb, hτl⟩ := fold_bound σ1.commit (uint.nat s.1) (L.drop k) hGd rfl
        (by rw [hst]; omega)
        (fun m' hm' hmc => hsmax m' (by rw [hdrop]; exact List.mem_append_left _ hm') hmc) hX
      rw [save_fail (τ := τ) (m := m) (by omega) _ hne hes] at hat
      cases hat
  · by_cases hk1 : k = L.length + 1
    · subst hk1
      have hdrop : (L.map Prod.fst ++ [WalOpG.snap m, WalOpG.save ⟨W64 0, W64 0, W64 0⟩ es]).drop
          (L.length + 1) = [WalOpG.save ⟨W64 0, W64 0, W64 0⟩ es] := by
        rw [List.drop_append, List.drop_of_length_le (by rw [hlen]; omega), hlen]
        simp
      rw [hdrop] at hat
      simp only [List.filter_cons, walKeep, decide_true, ↓reduceIte, List.filter_nil] at hat
      rw [save_fail (m := m) (by rw [hst]; omega) _ hne hes] at hat
      cases hat
    · have hdrop : (L.map Prod.fst ++ [WalOpG.snap m, WalOpG.save ⟨W64 0, W64 0, W64 0⟩ es]).drop k =
          [] := List.drop_of_length_le (by simp; omega)
      have hv : walValidSnaps (L.map Prod.fst ++ [WalOpG.snap m,
          WalOpG.save ⟨W64 0, W64 0, W64 0⟩ es]) k = [] := by
        unfold walValidSnaps
        rw [if_neg (by omega), hdrop]; rfl
      rw [hv] at hs
      cases hs

end pure

end etcd_wal
end EtcdGrove
end Perennial
