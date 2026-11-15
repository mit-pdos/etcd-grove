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

end pure

end etcd_wal
end EtcdGrove
end Perennial
