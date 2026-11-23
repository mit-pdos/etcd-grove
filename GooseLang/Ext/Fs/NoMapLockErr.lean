/-
The premise **no error of `flock`, `mmap`, `munmap` on chosen files** (`NoMapLockErr S`,
`Premises.lean`; pending the user's review) keeps a step from every state the semantics has one
from (`noMapLockErr_keeps : StepKeeps (NoMapLockErr S)`), so the specs hold over
`fsSemWithS (NoMapLockErr S) Q` and over its conjunction with `NoIoErr` (`stepKeeps_and`).
Untrusted.

The kept step, when the given one's outcome is not `MapLockOk`: for `flock`, the `MapLockOk`
outcome the premise names (every outcome of `flock` leaves the mappings as they were, so the heap
re-renders, `heapRendered_restamp`); for `mmap` (a failure), the success where the heap has room for
the mapping, the heap the given failure's with the new cells (`heapRendered_map`), and the step to
itself where it has none (`MmapStall`); for `munmap`, the success, the heap the given failure's but
for the mapping's cells, which are gone (`heapRendered_unmap`).
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
  exact lockStep_maps hl

/-- The `IoSet` covering every inode and every path. -/
def IoSet.all : IoSet := ⟨fun _ _ => True, fun _ => True⟩

/-- **`open` with no success ends with `EINTR`**: from a state where its arguments are accepted (a
step `hs`), `open` has the failure `EINTR`, the call ended and nothing else changed. -/
theorem isFsStep_open_eintr {v : val} {st : OsState} {e' : Expr} {st' : OsState}
    (hs : IsFsStep "Open" v st e' st') :
    ∃ st'', IsFsStep "Open" v st (osRes (#(-1 : w64)) EINTR) st'' ∧ st''.proc.maps = st.proc.maps := by
  simp only [IsFsStep] at hs ⊢
  rcases hs with ⟨p, fl, t, start, hv, htp, hfl, hc, htr, -⟩ | ⟨p, fl, t, start, hv, hn, ha, hro, hc, -⟩
  · exact ⟨st.metaEnd t, .inl ⟨p, fl, t, start, hv, htp, hfl, hc, htr,
      .inr ⟨EINTR, by decide, fun h => absurd h (by decide), rfl, .inl rfl⟩⟩, rfl⟩
  · exact ⟨st.metaEnd t, .inr ⟨p, fl, t, start, hv, hn, ha, hro, hc,
      .inr ⟨EINTR, by decide, rfl, rfl⟩⟩, rfl⟩

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

/-- **The heap after an `mmap`'s success, from the heap of its failure** (the given `h'`, rendered
for `st` itself), when the cells of the new mapping `mm` at `base` are free: those cells new, each
showing its byte of the file, every other cell as in `h'`. -/
theorem heapRendered_map (st : OsState) (base : Loc) (mm : OsMap) {h h' : GMap Loc (NonAtomic val)}
    (hr : HeapRendered st st h h') (hnone : st.proc.maps !! base = none)
    (hfree : ∀ k < mm.len, h !! (base +ₗ (k : Int)) = none) :
    ∃ h'', HeapRendered st (st.setProc { st.proc with maps := <[base := mm]> st.proc.maps })
      h h'' := by
  classical
  let st1 := st.setProc { st.proc with maps := <[base := mm]> st.proc.maps }
  obtain ⟨r1, r2, r3, r4⟩ := hr
  have hnew : ∀ k, k < mm.len → ¬ Mapped st (base +ₗ (k : Int)) := by
    rintro k hk ⟨i, b, hm⟩
    obtain ⟨m0, v0, h0, -⟩ := r1 _ i b hm ⟨i, b, hm⟩
    rw [hfree k hk] at h0; cases h0
  have hmaps1 : ∀ l i b, MapsTo st1 l i b ↔
      MapsTo st l i b ∨ (i = mm.ino ∧ b < mm.len ∧ l = base +ₗ (b : Int)) := by
    intro l i b
    constructor
    · rintro ⟨b0, m, h1, h2, h3, h4⟩
      simp only [st1, OsState.setProc, GMap.lookup_insert_eq_iff] at h1
      split at h1
      · rename_i heq; subst heq; cases h1; exact .inr ⟨h2.symm, h3, h4⟩
      · exact .inl ⟨b0, m, h1, h2, h3, h4⟩
    · rintro (⟨b0, m, h1, h2, h3, h4⟩ | ⟨rfl, h3, h4⟩)
      · refine ⟨b0, m, ?_, h2, h3, h4⟩
        simp only [st1, OsState.setProc, GMap.lookup_insert_eq_iff]
        split
        · rename_i heq; subst heq; rw [hnone] at h1; cases h1
        · exact h1
      · refine ⟨base, mm, ?_, rfl, h3, h4⟩
        simp only [st1, OsState.setProc, GMap.lookup_insert_eq_iff, if_true]
  let NewC : Loc → Prop := fun l => ∃ k, k < mm.len ∧ l = base +ₗ (k : Int)
  let h'' : GMap Loc (NonAtomic val) :=
    ⟨fun l => if hc : NewC l then some (Free (cellVal st1 mm.ino (Classical.choose hc)))
      else h'.lookup l, by
      obtain ⟨L, hL⟩ := h'.finite
      refine ⟨L ++ (List.range mm.len).map (fun k : Nat => base +ₗ (k : Int)), fun l hl => ?_⟩
      by_cases hc : NewC l
      · obtain ⟨k, hk, rfl⟩ := hc
        exact List.mem_append_right _ (List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩)
      · simp only [hc, dite_false] at hl
        exact List.mem_append_left _ (hL l hl)⟩
  have hl : ∀ l, h'' !! l = if hc : NewC l then
      some (Free (cellVal st1 mm.ino (Classical.choose hc))) else h' !! l := fun _ => rfl
  have hnewM : ∀ l, NewC l → ¬ Mapped st l := by rintro l ⟨k, hk, rfl⟩; exact hnew k hk
  refine ⟨h'', ?_, ?_, ?_, ?_⟩
  · intro l i b hm hM
    have hn : ¬ NewC l := fun hc => hnewM l hc hM
    have hm0 : MapsTo st l i b := by
      rcases (hmaps1 l i b).1 hm with hm0 | ⟨-, hb, rfl⟩
      · exact hm0
      · exact absurd ⟨b, hb, rfl⟩ hn
    obtain ⟨m, v0, hh, hh'⟩ := r1 l i b hm0 hM
    refine ⟨m, v0, hh, ?_⟩
    rw [hl, dif_neg hn, hh']
    rfl
  · intro l i b hm hM
    rcases (hmaps1 l i b).1 hm with hm0 | ⟨rfl, hb, rfl⟩
    · exact absurd ⟨i, b, hm0⟩ hM
    · have hc : NewC (base +ₗ (b : Int)) := ⟨b, hb, rfl⟩
      rw [hl, dif_pos hc]
      have hs := Classical.choose_spec hc
      have hb' : Classical.choose hc = b := by
        have := loc_add_inj base hs.2
        omega
      rw [hb']
  · intro l hM1 hM
    obtain ⟨i, b, hm⟩ := hM
    exact absurd ⟨i, b, (hmaps1 l i b).2 (.inl hm)⟩ hM1
  · intro l hM1 hM
    have hn : ¬ NewC l := by
      rintro ⟨k, hk, rfl⟩
      exact hM1 ⟨mm.ino, k, (hmaps1 _ _ _).2 (.inr ⟨rfl, hk, rfl⟩)⟩
    rw [hl, dif_neg hn]
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
  rcases hs with hs | ⟨ho, -, -, he, -, -⟩
  rotate_left
  · -- `mmap`'s step to itself is `MapLockOk`
    subst ho
    exact absurd (by simp only [MapLockOk]; exact Or.inr he) hok
  obtain ⟨hst, hfr, hr⟩ := hs
  unfold MapLockCovers at hcov
  split at hcov
  · -- Flock: the outcome the premise names, the heap re-rendered
    have h1 := isFsStep_flock_maps hst
    have h2 := isFsStep_flock_maps hs''
    obtain ⟨h'', hr''⟩ := heapRendered_restamp huniq h1 h2 hr
    exact ⟨e'', h'', st'', .inl ⟨hs'', mapsFresh_same h2, hr''⟩, fun _ _ => hz⟩
  · -- Mmap: the given step is a failure (not `MapLockOk`); the success where the heap has room,
    -- the step to itself where it has none
    simp only [IsFsStep] at hst
    obtain ⟨fd, off, len, prot, fl, d, hv, hfd, hrd, hoff, hlen, hprot, hfl, hres⟩ := hst
    rcases hres with ⟨base, -, -, -, -, he⟩ | ⟨e, he0, hst', he⟩
    · exact absurd (Or.inl ⟨_, he⟩) hok
    · subst st'
      have hargs : IsFsStep "Mmap" v st e' st := by
        simp only [IsFsStep]
        exact ⟨fd, off, len, prot, fl, d, hv, hfd, hrd, hoff, hlen, hprot, hfl,
          .inr ⟨e, he0, by trivial, he⟩⟩
      by_cases hroom : MmapRoom st h len.toNat
      · obtain ⟨base, hpos, hal, hnone, hmax, hfree⟩ := hroom
        obtain ⟨h'', hr''⟩ := heapRendered_map st base ⟨d.ino, len.toNat⟩ hr hnone hfree
        refine ⟨osRes (#base) 0, h'', st.setProc { st.proc with
            maps := <[base := ⟨d.ino, len.toNat⟩]> st.proc.maps,
            mapDesc := <[base := .live fd]> st.proc.mapDesc }, .inl ⟨?_, ?_, hr''⟩,
          fun _ _ => Or.inl ⟨_, rfl⟩⟩
        · simp only [IsFsStep]
          exact ⟨fd, off, len, prot, fl, d, hv, hfd, hrd, hoff, hlen, hprot, hfl,
            .inl ⟨base, hpos, hal, hnone, rfl, rfl⟩⟩
        · intro b m h1 h2
          simp only [OsState.setProc, GMap.lookup_insert_eq_iff] at h1
          split at h1
          · rename_i heq; subst heq; cases h1; exact ⟨hmax, hfree⟩
          · rw [h1] at h2; cases h2
      · exact ⟨ExternalOp fsExt.name "Mmap" (Val v), h, st,
          .inr ⟨rfl, ⟨_, _, hargs⟩, ⟨fd, off, len, prot, fl, hv, hroom⟩, rfl, rfl, rfl⟩,
          fun _ _ => Or.inr rfl⟩
  · -- Munmap: the given step is a failure; the success
    simp only [IsFsStep] at hst
    obtain ⟨base, len, cap, m, hv, hm, hlen, hcap, hres⟩ := hst
    have hsucc : ∀ h2 : GMap Loc (NonAtomic val),
        HeapRendered st (st.setProc
          { st.proc with maps := GMap.delete base st.proc.maps, mapDesc := GMap.delete base st.proc.mapDesc })
          h h2 →
        ∃ e'' h'' st'', FsStep "Munmap" v h st () e'' h'' st'' () ∧
          NoMapLockErr S "Munmap" v st e'' st'' := by
      intro h2 hr2
      refine ⟨Val (#(0 : w64)), h2, _, .inl ⟨?_, ?_, hr2⟩, fun _ _ => (rfl : Val (#(0 : w64)) = _)⟩
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
  · -- Open (no free fd): the outcome the premise names, the heap re-rendered
    have h1 := isFsStep_open_maps hst
    have h2 := isFsStep_open_maps hs''
    obtain ⟨h'', hr''⟩ := heapRendered_restamp huniq h1 h2 hr
    exact ⟨e'', h'', st'', .inl ⟨hs'', mapsFresh_same h2, hr''⟩, fun _ _ => hz⟩
  · -- Madvise: the outcome the premise names (no outcome changes anything)
    have hm : ∀ {e1 st1}, IsFsStep "Madvise" v st e1 st1 → st1.proc.maps = st.proc.maps := by
      intro e1 st1 h1; simp only [IsFsStep] at h1; obtain ⟨_, _, _, _, -, -, rfl, -⟩ := h1; rfl
    obtain ⟨h'', hr''⟩ := heapRendered_restamp huniq (hm hst) (hm hs'') hr
    exact ⟨e'', h'', st'', .inl ⟨hs'', mapsFresh_same (hm hs''), hr''⟩, fun _ _ => hz⟩
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

/-- **`NoIoErr` and `NoMapLockErr` keep steps together.** They name disjoint operations but `open`
(`stepKeeps_and`): `flock`, `mmap`, `munmap`, `madvise` only `NoMapLockErr`; `open` from a state with
a free fd and the rest only `NoIoErr`. An `open` with no free fd (both may name it): its outcome with
errno 0 if the semantics has one (both hold of it), and otherwise its `EINTR` (`NoIoErr` then says
nothing). -/
theorem noIoErr_noMapLockErr_keeps (S T : IoSet) :
    StepKeeps (StepPrem.and (NoIoErr S) (NoMapLockErr T)) := by
  intro _ _ o v h st e' h' st' huniq hs
  by_cases hO : o = "Open" ∧ ∀ fd, ¬ FdFree st fd
  · obtain ⟨rfl, hnf⟩ := hO
    obtain ⟨hst, -, hr⟩ := fsStepV_of_ne (by decide) hs
    by_cases hz : ∃ e'' st'', IsFsStep "Open" v st e'' st'' ∧ ErrnoZero "Open" e''
    · obtain ⟨e'', st'', hs'', hz''⟩ := hz
      obtain ⟨h'', hr''⟩ := heapRendered_restamp huniq (isFsStep_open_maps hst) (isFsStep_open_maps hs'') hr
      exact ⟨e'', h'', st'', .inl ⟨hs'', mapsFresh_same (isFsStep_open_maps hs''), hr''⟩,
        fun _ => ⟨fun _ => hz'', fun hn => absurd ⟨e'', st'', hs'', hz''⟩ hn⟩, fun _ _ => Or.inl hz''⟩
    · obtain ⟨st'', hs'', hm''⟩ := isFsStep_open_eintr hst
      obtain ⟨h'', hr''⟩ := heapRendered_restamp huniq (isFsStep_open_maps hst) hm'' hr
      -- `PathErrno`'s `open` case asks for a free fd
      have hpe : PathErrno "Open" v st (osRes (#(-1 : w64)) EINTR) := by
        simp only [IsFsStep] at hst
        rcases hst with ⟨p, fl, t, -, hv, -⟩ | ⟨p, fl, t, -, hv, -⟩ <;>
          exact ⟨t, p, fl, hv, fun h => absurd h.2.2.2 (fun ⟨fd, hf⟩ => hnf fd hf)⟩
      exact ⟨_, h'', st'', .inl ⟨hs'', mapsFresh_same hm'', hr''⟩,
        fun _ => ⟨fun hex => absurd hex hz, fun _ => hpe⟩, fun _ _ => Or.inr rfl⟩
  have hdisj : (∀ e' st', NoIoErr S o v st e' st') ∨ (∀ e' st', NoMapLockErr T o v st e' st') := by
    by_cases ho : o = "Flock" ∨ o = "Mmap" ∨ o = "Munmap" ∨ o = "Madvise"
    · left
      intro e' st' hc
      unfold IoCovers at hc
      rcases ho with rfl | rfl | rfl | rfl <;> exact hc.elim
    · right
      intro e' st' hc
      unfold MapLockCovers at hc
      split at hc
      · exact absurd (Or.inl rfl) ho
      · exact absurd (Or.inr (Or.inl rfl)) ho
      · exact absurd (Or.inr (Or.inr (Or.inl rfl))) ho
      · exact absurd ⟨rfl, hc.2⟩ hO
      · exact absurd (Or.inr (Or.inr (Or.inr rfl))) ho
      · exact hc.elim
  rcases hdisj with hp | hq
  · obtain ⟨e'', h'', st'', hs'', hq⟩ := noMapLockErr_keeps T o v h st e' h' st' huniq hs
    exact ⟨e'', h'', st'', hs'', hp _ _, hq⟩
  · obtain ⟨e'', h'', st'', hs'', hp⟩ := noIoErr_keeps S o v h st e' h' st' huniq hs
    exact ⟨e'', h'', st'', hs'', hp, hq _ _⟩

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
