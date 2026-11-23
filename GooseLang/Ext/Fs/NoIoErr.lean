/-
The premise **no I/O error on chosen files** (`NoIoErr S`, `Premises.lean`) keeps a step from every
state the semantics has one from (`noIoErr_keeps : StepKeeps (NoIoErr S)`): the specs and the
adequacy theorem `fsSQ_crash_adequacy` hold over `fsSemWithS (NoIoErr S) Q`. Untrusted.

The proof needs no case of the semantics' successes: the premise only asks for errno 0 when the
semantics has an outcome with errno 0 (`ErrnoZero`) for the call from that state, so the step it keeps
is that outcome when there is one and the given step otherwise. What is left is that the kept outcome
is a step with the heap (`FsStep`): every covered operation leaves the mappings as they were
(`isFsStep_maps`), and a heap rendered for one outcome is re-rendered for another with the same
mappings (`heapRendered_restamp`).
-/
module

public import GooseLang.Ext.Fs.FilteredSem
public import GooseLang.Ext.Fs.Facts

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

section keeps
variable [GooseExts] [GoGlobalContext]

theorem mapsTo_maps {st st' : OsState} (h : st'.proc.maps = st.proc.maps) (l : Loc) (i : Ino)
    (b : Nat) : MapsTo st' l i b ↔ MapsTo st l i b := by
  simp only [MapsTo, h]

theorem mapped_maps {st st' : OsState} (h : st'.proc.maps = st.proc.maps) (l : Loc) :
    Mapped st' l ↔ Mapped st l := by
  simp only [Mapped, mapsTo_maps h]

/-- A heap rendered for a step from `st` to `st'` is re-rendered for a step to `st''` with the same
mappings: each mapped cell (in its mode) shows `st''`'s file. -/
theorem heapRendered_restamp {st st' st'' : OsState} {h h' : GMap Loc (NonAtomic val)}
    (huniq : ∀ l i b i' b', MapsTo st l i b → MapsTo st l i' b' → i = i' ∧ b = b')
    (h1 : st'.proc.maps = st.proc.maps) (h2 : st''.proc.maps = st.proc.maps)
    (hr : HeapRendered st st' h h') : ∃ h'', HeapRendered st st'' h h'' := by
  classical
  let f : Loc → NonAtomic val → NonAtomic val := fun l x =>
    if hM : Mapped st l then (x.1, cellVal st'' hM.choose hM.choose_spec.choose) else x
  let h'' : GMap Loc (NonAtomic val) :=
    ⟨fun l => (h'.lookup l).map (f l), by
      obtain ⟨L, hL⟩ := h'.finite
      exact ⟨L, fun k hk => hL k (by simpa using hk)⟩⟩
  have hl : ∀ l, h'' !! l = (h' !! l).map (f l) := fun _ => rfl
  obtain ⟨r1, r2, r3, r4⟩ := hr
  refine ⟨h'', ?_, ?_, ?_, ?_⟩
  · intro l i b hm hM
    obtain ⟨m, v0, hh, hh'⟩ := r1 l i b ((mapsTo_maps h1 l i b).2 ((mapsTo_maps h2 l i b).1 hm)) hM
    refine ⟨m, v0, hh, ?_⟩
    rw [hl, hh']
    simp only [Option.map_some, f, dif_pos hM, Option.some.injEq, Prod.mk.injEq, true_and]
    obtain ⟨hi, hb⟩ := huniq l _ _ i b hM.choose_spec.choose_spec ((mapsTo_maps h2 l i b).1 hm)
    subst hi; subst hb; rfl
  · intro l i b hm hM
    exact absurd ⟨i, b, (mapsTo_maps h2 l i b).1 hm⟩ hM
  · intro l hM hM'
    exact absurd ((mapped_maps h2 l).2 hM') hM
  · intro l hM hM'
    rw [hl, r4 l (fun h => hM ((mapped_maps h2 l).2 ((mapped_maps h1 l).1 h))) hM']
    cases h !! l with
    | none => rfl
    | some x => simp only [Option.map_some, f]; rw [dif_neg hM']

/-- `open`'s effect before its fd leaves the mappings. -/
theorem openEffect_maps {st : OsState} {p : GoString} {acc : Nat} {creat trunc : Bool} {start : Nat}
    {st1 : OsState} {tgt : Node} (h : OpenEffect st p acc creat trunc start st1 tgt) :
    st1.proc.maps = st.proc.maps := by
  unfold OpenEffect at h
  split at h
  · obtain ⟨-, -, -, rfl, -⟩ := h; rfl
  · obtain ⟨⟨f, -, rfl⟩, -⟩ := h
    split <;> rfl
  · obtain ⟨-, j, b, -, rfl, -⟩ := h; rfl

/-- A lock request's step leaves the mappings. -/
theorem lockStep_maps {st : OsState} {k : LockKind} {fd : w64} {d : OsFd} {req : Option Bool}
    {nb : Bool} {w e' : Expr} {st' : OsState} (h : LockStep st k fd d req nb w e' st') :
    st'.proc.maps = st.proc.maps := by
  unfold LockStep at h
  cases req with
  | some ex => rcases h with ⟨-, ⟨-, rfl, -⟩ | ⟨e, -, rfl, -⟩ | ⟨-, -, rfl, -⟩⟩ <;> rfl
  | none => rcases h with ⟨rfl, -⟩ | ⟨e, -, -, rfl | rfl⟩ <;> rfl

/-- Every outcome of `open` leaves the mappings as they were. -/
theorem isFsStep_open_maps {v : val} {st : OsState} {e' : Expr} {st' : OsState}
    (hs : IsFsStep "Open" v st e' st') : st'.proc.maps = st.proc.maps := by
  simp only [IsFsStep] at hs
  rcases hs with ⟨p, fl, t, start, -, -, -, -, -, ⟨st1, tgt, fd, he, -, rfl, -⟩ | ⟨e, -, -, -, rfl | ⟨tgt, he⟩⟩⟩ |
    ⟨p, fl, t, start, -, -, -, -, -, ⟨fd, -, rfl, -⟩ | ⟨e, -, rfl, -⟩⟩
  · have : st1.proc.maps = st.proc.maps := (openEffect_maps he).trans rfl
    cases tgt <;> exact this
  · rfl
  · exact (openEffect_maps he).trans rfl
  · rfl
  · rfl

/-- Every operation `IoCovers` names leaves the mappings as they were. -/
theorem isFsStep_maps {S : IoSet} {o : String} {v : val} {st : OsState} {e' : Expr} {st' : OsState}
    (hc : IoCovers S o v st) (hs : IsFsStep o v st e' st') : st'.proc.maps = st.proc.maps := by
  unfold IoCovers at hc
  split at hc <;> simp only [IsFsStep] at hs
  · -- Fsync
    obtain ⟨fd, d, f, -, -, -, ⟨rfl, -⟩ | ⟨e, -, -, -, rfl⟩⟩ := hs <;> rfl
  · -- Close
    obtain ⟨fd, e, d, -, -, rfl, -⟩ := hs; rfl
  · -- Fstat
    obtain ⟨fd, d, sz, -, -, -, rfl, -⟩ := hs; rfl
  · -- PRead
    obtain ⟨fd, off, n, d, r, -, -, -, -, -, rfl, -⟩ := hs; rfl
  · -- PWriteFinish
    obtain ⟨t, c, off, data, f, k, e, -, -, -, -, -, -, -, -, rfl, -⟩ := hs; rfl
  · -- FtruncateFinish
    obtain ⟨t, c, sz, f, -, -, -, -, ⟨-, rfl, -⟩ | ⟨e, -, -, rfl | ⟨-, rfl⟩⟩⟩ := hs <;> rfl
  · -- FallocFinish
    obtain ⟨t, c, sz, f, -, -, -, -, ⟨-, rfl, -⟩ | ⟨e, -, -, rfl | ⟨-, w, -, -, rfl⟩⟩⟩ := hs <;> rfl
  · -- DirSync
    obtain ⟨fd, df, -, -, ⟨rfl, -⟩ | ⟨e, -, -, rfl⟩⟩ := hs <;> rfl
  · -- DirClose
    obtain ⟨fd, e, df, -, -, rfl, -⟩ := hs; rfl
  · -- Open
    exact isFsStep_open_maps hs
  · -- Rename
    obtain ⟨s, t, k, start, -, -, -, -, -, -, h⟩ := hs
    rcases h with ⟨-, o, -, ⟨rfl, -⟩ | ⟨e, -, -, rfl | rfl⟩⟩ | ⟨-, -, rfl, -⟩ | ⟨e, -, -, rfl⟩ <;> rfl
  · -- Mkdir
    obtain ⟨p, k, start, -, -, -, h⟩ := hs
    rcases h with ⟨j, b, -, -, ⟨rfl, -⟩ | ⟨e, -, -, rfl | rfl⟩⟩ | ⟨e, -, -, rfl⟩ <;> rfl
  · -- Unlink
    obtain ⟨p, k, start, -, -, -, h⟩ := hs
    rcases h with ⟨i, j, b, -, -, ⟨rfl, -⟩ | ⟨e, -, -, rfl | rfl⟩⟩ | ⟨e, -, -, rfl⟩ <;> rfl
  · -- Rmdir
    obtain ⟨p, k, start, -, -, -, h⟩ := hs
    rcases h with ⟨j', j, b, -, -, ⟨rfl, -⟩ | ⟨e, -, -, rfl | rfl⟩⟩ | ⟨e, -, -, rfl⟩ <;> rfl
  · -- OfdLock
    obtain ⟨fd, cmd, typ, d, req, -, -, -, -, -, -, h⟩ := hs; exact lockStep_maps h
  · -- DirReadNext
    obtain ⟨fd, df, u, s, r, -, -, -, h⟩ := hs
    rcases h with ⟨b, -, -, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨e, -, -, rfl, -⟩ <;> rfl
  · exact hc.elim

/-- A covered call has an outcome satisfying what `NoIoErr` asks of it. -/
theorem noIoErr_good {S : IoSet} {o : String} {v : val} {st : OsState} {e' : Expr} {st' : OsState}
    (hs : IsFsStep o v st e' st') :
    ∃ e'' st'', IsFsStep o v st e'' st'' ∧
      ((∃ e'' st'', IsFsStep o v st e'' st'' ∧ ErrnoZero o e'') → ErrnoZero o e'') ∧
      (¬ (∃ e'' st'', IsFsStep o v st e'' st'' ∧ ErrnoZero o e'') → PathErrno o v st e'') := by
  by_cases hsucc : ∃ e'' st'', IsFsStep o v st e'' st'' ∧ ErrnoZero o e''
  · obtain ⟨e'', st'', hs'', hz⟩ := hsucc
    exact ⟨e'', st'', hs'', fun _ => hz, fun h => absurd ⟨e'', st'', hs'', hz⟩ h⟩
  have hno : (∃ e'' st'', IsFsStep o v st e'' st'' ∧ ErrnoZero o e'') → ∀ x : Expr, ErrnoZero o x :=
    fun h => absurd h hsucc
  by_cases hu : o = "Unlink"
  · subst hu
    have hs0 := hs
    simp only [IsFsStep] at hs
    obtain ⟨p, k, start, hv, htn, hc, -⟩ := hs
    let e0 : w64 := if st.lookup p = none then ENOENT else EISDIR
    have he0 : e0 ≠ 0 := by
      show (if st.lookup p = none then ENOENT else EISDIR) ≠ 0
      split <;> decide
    refine ⟨Val (#e0), st.metaEnd k, ?_, fun h => hno h _, fun _ => ?_⟩
    · simp only [IsFsStep]
      exact ⟨p, k, start, hv, htn, hc, .inr ⟨e0, he0, rfl, rfl⟩⟩
    · refine ⟨k, p, hv, ?_⟩
      refine ⟨fun h => ?_, fun ⟨j, h⟩ => ?_⟩
      · show Val (#(if st.lookup p = none then ENOENT else EISDIR)) = _
        rw [if_pos h.1]
      · show Val (#(if st.lookup p = none then ENOENT else EISDIR)) = _
        rw [if_neg (by rw [h]; exact Option.some_ne_none _)]
  by_cases hr : o = "Rmdir"
  · subst hr
    simp only [IsFsStep] at hs
    obtain ⟨p, k, start, hv, htn, hc, -⟩ := hs
    let e0 : w64 := if st.lookup p = none then ENOENT else ENOTEMPTY
    have he0 : e0 ≠ 0 := by
      show (if st.lookup p = none then ENOENT else ENOTEMPTY) ≠ 0
      split <;> decide
    refine ⟨Val (#e0), st.metaEnd k, ?_, fun h => hno h _, fun _ => ?_⟩
    · simp only [IsFsStep]
      exact ⟨p, k, start, hv, htn, hc, .inr ⟨e0, he0, rfl, rfl⟩⟩
    · refine ⟨k, p, hv, ?_⟩
      refine ⟨fun h => ?_, fun ⟨j, b, n, h, _⟩ => ?_⟩
      · show Val (#(if st.lookup p = none then ENOENT else ENOTEMPTY)) = _
        rw [if_pos h.1]
      · show Val (#(if st.lookup p = none then ENOENT else ENOTEMPTY)) = _
        rw [if_neg (by rw [h]; exact Option.some_ne_none _)]
  by_cases ho : o = "Open"
  · subst ho
    have hs0 := hs
    simp only [IsFsStep] at hs
    rcases hs with ⟨p, fl, t, start, hv, htp, hfl, hc, htr, -⟩ |
      ⟨p, fl, t, start, hv, hntp, hab, hfl, hc, -⟩ <;>
    by_cases hA : fl.toNat / O_CREAT % 2 = 0 ∧ st.lookup p = none ∧ st.ParentDir p ∧
      ∃ fd, FdFree st fd
    · refine ⟨osRes (#(-1 : w64)) ENOENT, st.metaEnd t, ?_, fun h => hno h _,
        fun _ => ⟨t, p, fl, hv, fun _ => rfl⟩⟩
      simp only [IsFsStep]
      exact .inl ⟨p, fl, t, start, hv, htp, hfl, hc, htr,
        .inr ⟨ENOENT, by decide, fun _ => hA.2.1, rfl, .inl rfl⟩⟩
    · exact ⟨e', st', hs0, fun h => hno h _, fun _ => ⟨t, p, fl, hv, fun h => absurd h hA⟩⟩
    · refine ⟨osRes (#(-1 : w64)) ENOENT, st.metaEnd t, ?_, fun h => hno h _,
        fun _ => ⟨t, p, fl, hv, fun _ => rfl⟩⟩
      simp only [IsFsStep]
      exact .inr ⟨p, fl, t, start, hv, hntp, hab, hfl, hc, .inr ⟨ENOENT, by decide, rfl, rfl⟩⟩
    · exact ⟨e', st', hs0, fun h => hno h _, fun _ => ⟨t, p, fl, hv, fun h => absurd h hA⟩⟩
  refine ⟨e', st', hs, fun h => hno h _, fun _ => ?_⟩
  unfold PathErrno
  split
  · exact absurd rfl hu
  · exact absurd rfl hr
  · exact absurd rfl ho
  · trivial

end keeps

/-- **`NoIoErr S` keeps a step** (see the file header). -/
theorem noIoErr_keeps (S : IoSet) : StepKeeps (NoIoErr S) := by
  intro _ _ o v h st e' h' st' huniq hs
  by_cases hc : IoCovers S o v st
  · have hs := fsStepV_of_ne (by rintro rfl; simp [IoCovers] at hc) hs
    obtain ⟨e'', st'', hs'', hz, hp⟩ := noIoErr_good (S := S) hs.1
    have h1 := isFsStep_maps hc hs.1
    have h2 := isFsStep_maps hc hs''
    obtain ⟨h'', hr⟩ := heapRendered_restamp huniq h1 h2 hs.2.2
    exact ⟨e'', h'', st'', .inl ⟨hs'', mapsFresh_same h2, hr⟩, fun _ => ⟨hz, hp⟩⟩
  · exact ⟨e', h', st', hs, fun hc' => absurd hc' hc⟩

end Fs
end Perennial

end
