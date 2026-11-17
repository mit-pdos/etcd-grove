/-
The premise **no error of `flock`, `mmap`, `munmap` on chosen files** (`NoMapLockErr S`,
`Premises.lean`; pending the user's review) keeps a step from every state the semantics has one
from (`noMapLockErr_keeps : StepKeeps (NoMapLockErr S)`), so the specs hold over
`fsSemWithS (NoMapLockErr S) Q` and over its conjunction with `NoIoErr` (`stepKeeps_and`).
Untrusted.

The kept step, when the given one's outcome is not `MapLockOk`: for `flock`, the `MapLockOk`
outcome the premise names (every outcome of `flock` leaves the mappings as they were, so the heap
re-renders, `heapRendered_restamp`); for `mmap`, the failure with `ENOMEM` (a failure leaves the
state and the heap as the given failure does); for `munmap`, the success, the heap the given
failure's but for the mapping's cells, which are gone (`heapRendered_unmap`).
-/
module

public import GooseLang.Ext.Fs.NoIoErr

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

section keeps
variable [GooseExts] [GoGlobalContext]

/-- Every outcome of `flock` leaves the mappings as they were. -/
theorem isFsStep_flock_maps {v : val} {st : OsState} {e' : Expr} {st' : OsState}
    (hs : IsFsStep "Flock" v st e' st') : st'.proc.maps = st.proc.maps := by
  simp only [IsFsStep] at hs
  obtain ⟨fd, how, d, req, nb, -, -, -, hl⟩ := hs
  unfold LockStep at hl
  rcases req with _ | ex
  · rcases hl with ⟨rfl, -⟩ | ⟨e, -, -, rfl | rfl⟩ <;> rfl
  · obtain ⟨-, ⟨-, rfl, -⟩ | ⟨e, -, -, rfl, -⟩⟩ := hl <;> rfl

/-- `cellVal` does not read the mappings. -/
theorem cellVal_setMaps (st : OsState) (M : GMap Loc OsMap) (i : Ino) (b : Nat) :
    cellVal (st.setProc { st.proc with maps := M }) i b = cellVal st i b := rfl

/-- **The heap after an `munmap`'s success, from the heap of its failure that kept the mapping**
(the given `h'`, rendered for `st` itself): the mapping's cells gone, every other cell as in `h'`. -/
theorem heapRendered_unmap (st : OsState) (base : Loc) {h h' : GMap Loc (NonAtomic val)}
    (hr : HeapRendered st st h h') :
    ∃ h'', HeapRendered st (st.setProc { st.proc with maps := GMap.delete base st.proc.maps })
      h h'' := by
  classical
  let st1 := st.setProc { st.proc with maps := GMap.delete base st.proc.maps }
  have hsub : ∀ l i b, MapsTo st1 l i b → MapsTo st l i b := by
    rintro l i b ⟨b0, m, h1, h2, h3, h4⟩
    simp only [st1, OsState.setProc, GMap.lookup_delete_iff] at h1
    split at h1
    · cases h1
    · exact ⟨b0, m, h1, h2, h3, h4⟩
  let h'' : GMap Loc (NonAtomic val) :=
    ⟨fun l => if Mapped st l ∧ ¬ Mapped st1 l then none else h'.lookup l, by
      obtain ⟨L, hL⟩ := h'.finite
      refine ⟨L, fun k hk => hL k ?_⟩
      split at hk
      · simp at hk
      · exact hk⟩
  have hl : ∀ l, h'' !! l = if Mapped st l ∧ ¬ Mapped st1 l then none else h' !! l := fun _ => rfl
  obtain ⟨r1, r2, r3, r4⟩ := hr
  refine ⟨h'', ?_, ?_, ?_, ?_⟩
  · intro l i b hm hM
    obtain ⟨m, v0, hh, hh'⟩ := r1 l i b (hsub l i b hm) hM
    refine ⟨m, v0, hh, ?_⟩
    have hn : ¬ (Mapped st l ∧ ¬ Mapped st1 l) := fun h => h.2 ⟨i, b, hm⟩
    simp only [hl, hn, ↓reduceIte, hh']
    rfl
  · intro l i b hm hM
    exact absurd ⟨i, b, hsub l i b hm⟩ hM
  · intro l hM1 hM
    have hy : Mapped st l ∧ ¬ Mapped st1 l := ⟨hM, hM1⟩
    rw [hl]
    split
    · rfl
    · contradiction
  · intro l hM1 hM
    have hn : ¬ (Mapped st l ∧ ¬ Mapped st1 l) := fun h => hM h.1
    simp only [hl, hn, ↓reduceIte]
    exact r4 l hM hM

end keeps

/-- **`NoMapLockErr S` keeps a step** (see the file header). -/
theorem noMapLockErr_keeps (S : IoSet) : StepKeeps (NoMapLockErr S) := by
  intro _ _ o v h st e' h' st' huniq hs
  by_cases hok : MapLockOk o v e'
  · exact ⟨e', h', st', hs, fun _ _ => hok⟩
  by_cases hc : MapLockCovers S o v st ∧ ∃ e'' st'', IsFsStep o v st e'' st'' ∧ MapLockOk o v e''
  rotate_left
  · exact ⟨e', h', st', hs, fun hc' hex => absurd ⟨hc', hex⟩ hc⟩
  obtain ⟨hcov, e'', st'', hs'', hz⟩ := hc
  obtain ⟨hst, hfr, hr⟩ := hs
  unfold MapLockCovers at hcov
  split at hcov
  · -- Flock: the outcome the premise names, the heap re-rendered
    have h1 := isFsStep_flock_maps hst
    have h2 := isFsStep_flock_maps hs''
    obtain ⟨h'', hr''⟩ := heapRendered_restamp huniq h1 h2 hr
    exact ⟨e'', h'', st'', ⟨hs'', mapsFresh_same h2, hr''⟩, fun _ _ => hz⟩
  · -- Mmap: the given step is a failure (not `MapLockOk`); the same failure with `ENOMEM`
    simp only [IsFsStep] at hst
    obtain ⟨fd, off, len, prot, fl, d, hv, hfd, hrd, hoff, hlen, hprot, hfl, hres⟩ := hst
    rcases hres with ⟨base, -, -, -, -, he⟩ | ⟨e, -, hst', he⟩
    · exact absurd (Or.inl ⟨_, he⟩) hok
    · refine ⟨osRes (#null) ENOMEM, h', st', ⟨?_, hfr, hr⟩, fun _ _ => Or.inr rfl⟩
      simp only [IsFsStep]
      exact ⟨fd, off, len, prot, fl, d, hv, hfd, hrd, hoff, hlen, hprot, hfl,
        .inr ⟨ENOMEM, by decide, hst', rfl⟩⟩
  · -- Munmap: the given step is a failure; the success
    simp only [IsFsStep] at hst
    obtain ⟨base, len, cap, m, hv, hm, hlen, hcap, hres⟩ := hst
    have hsucc : ∀ h2 : GMap Loc (NonAtomic val),
        HeapRendered st (st.setProc { st.proc with maps := GMap.delete base st.proc.maps }) h h2 →
        ∃ e'' h'' st'', FsStep "Munmap" v h st () e'' h'' st'' () ∧
          NoMapLockErr S "Munmap" v st e'' st'' := by
      intro h2 hr2
      refine ⟨Val (#(0 : w64)), h2, _, ⟨?_, ?_, hr2⟩, fun _ _ => (rfl : Val (#(0 : w64)) = _)⟩
      · simp only [IsFsStep]
        refine ⟨base, len, cap, m, hv, hm, hlen, hcap, .inl ⟨?_, ?_⟩⟩ <;> trivial
      · intro b m1 h1 h0
        simp only [OsState.setProc, GMap.lookup_delete_iff] at h1
        split at h1
        · cases h1
        · rw [h1] at h0; cases h0
    rcases hres with ⟨-, he⟩ | ⟨e, -, he, hst' | hst'⟩
    · exact absurd he hok
    · rw [hst'] at hr
      obtain ⟨h2, hr2⟩ := heapRendered_unmap st base hr
      exact hsucc h2 hr2
    · rw [hst'] at hr
      exact hsucc h' hr
  · exact hcov.elim

/-- Two premises on steps, together. -/
def StepPrem.and (P Q : StepPrem) : StepPrem := fun o v st e' st' => P o v st e' st' ∧ Q o v st e' st'

/-- **Two premises that keep steps keep them together** when they constrain different operations:
every step of one's operations satisfies the other (`hPQ`, `hQP`, as `NoIoErr` and `NoMapLockErr`,
which name disjoint operations: `noIoErr_noMapLockErr_keeps`). -/
theorem stepKeeps_and (P Q : StepPrem) (hP : StepKeeps P) (hQ : StepKeeps Q)
    (hdisj : ∀ [GooseExts] [GoGlobalContext] (o : String) (v : val) (st : OsState),
      (∀ e' st', P o v st e' st') ∨ (∀ e' st', Q o v st e' st')) :
    StepKeeps (StepPrem.and P Q) := by
  intro _ _ o v h st e' h' st' huniq hs
  rcases hdisj o v st with hp | hq
  · obtain ⟨e'', h'', st'', hs'', hq⟩ := hQ o v h st e' h' st' huniq hs
    exact ⟨e'', h'', st'', hs'', hp _ _, hq⟩
  · obtain ⟨e'', h'', st'', hs'', hp⟩ := hP o v h st e' h' st' huniq hs
    exact ⟨e'', h'', st'', hs'', hp, hq _ _⟩

/-- `NoIoErr` and `NoMapLockErr` name disjoint operations, so they keep steps together. -/
theorem noIoErr_noMapLockErr_keeps (S T : IoSet) :
    StepKeeps (StepPrem.and (NoIoErr S) (NoMapLockErr T)) := by
  refine stepKeeps_and _ _ (noIoErr_keeps S) (noMapLockErr_keeps T) ?_
  intro _ _ o v st
  by_cases ho : o = "Flock" ∨ o = "Mmap" ∨ o = "Munmap"
  · left
    intro e' st' hc
    unfold IoCovers at hc
    rcases ho with rfl | rfl | rfl <;> exact hc.elim
  · right
    intro e' st' hc
    unfold MapLockCovers at hc
    split at hc
    · exact absurd (Or.inl rfl) ho
    · exact absurd (Or.inr (Or.inl rfl)) ho
    · exact absurd (Or.inr (Or.inr rfl)) ho
    · exact hc.elim

/-- A semantics whose steps satisfy two premises together satisfies each. -/
theorem fsStepSat_and_left (P Q : StepPrem) [S : ExtSemantics fsExt] [h : FsStepSat (StepPrem.and P Q)] :
    FsStepSat P :=
  ⟨fun o v h0 st g e' h' st' g' hs => (h.sat o v h0 st g e' h' st' g' hs).1⟩

theorem fsStepSat_and_right (P Q : StepPrem) [S : ExtSemantics fsExt] [h : FsStepSat (StepPrem.and P Q)] :
    FsStepSat Q :=
  ⟨fun o v h0 st g e' h' st' g' hs => (h.sat o v h0 st g e' h' st' g' hs).2⟩

end Fs
end Perennial

end
