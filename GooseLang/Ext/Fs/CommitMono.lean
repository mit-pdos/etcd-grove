/-
Every step of the Linux file extension keeps the committed entries of the tree's log committed (a
directory `fsync` only adds to them; `IsFsStep`, `Impl.lean`). Untrusted.
-/
module

public import GooseLang.Ext.Fs.Impl

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

/-- `st'` has every entry `st` has committed committed. -/
def CommitGrows (st st' : OsState) : Prop := ∀ y, st.fs.committed y → st'.fs.committed y

theorem commitGrows_of_eq {st st' : OsState} (h : st'.fs.committed = st.fs.committed) :
    CommitGrows st st' := fun _ hy => h ▸ hy

theorem commitGrows_refl (st : OsState) : CommitGrows st st := fun _ hy => hy

theorem commitGrows_trans {st st' st'' : OsState} (h1 : CommitGrows st st')
    (h2 : CommitGrows st' st'') : CommitGrows st st'' := fun y hy => h2 y (h1 y hy)

@[simp] theorem committed_setFile (st : OsState) (i : Ino) (f : OsFile) :
    (st.setFile i f).fs.committed = st.fs.committed := rfl
@[simp] theorem committed_stampFile (st : OsState) (i : Ino) (g : Nat → OsFile) :
    (st.stampFile i g).fs.committed = st.fs.committed := rfl
@[simp] theorem committed_setProc (st : OsState) (p : ProcState) :
    (st.setProc p).fs.committed = st.fs.committed := rfl
@[simp] theorem committed_metaEnd (st : OsState) (t : Nat) :
    (st.metaEnd t).fs.committed = st.fs.committed := rfl
@[simp] theorem committed_metaDo (st : OsState) (o : MetaOp) (s : Nat) :
    (st.metaDo o s).fs.committed = st.fs.committed := rfl
@[simp] theorem committed_takeIno (st : OsState) :
    st.takeIno.fs.committed = st.fs.committed := rfl
@[simp] theorem committed_doneInflight (st : OsState) (t : Nat) :
    (st.doneInflight t).fs.committed = st.fs.committed := rfl
@[simp] theorem committed_addInflight (st : OsState) (t : Nat) (c : OsChange) :
    (st.addInflight t c).fs.committed = st.fs.committed := rfl

theorem openEffect_committed {st : OsState} {p : GoString} {acc : Nat} {creat trunc : Bool}
    {start : Nat} {st1 : OsState} {tgt : Node} (h : OpenEffect st p acc creat trunc start st1 tgt) :
    st1.fs.committed = st.fs.committed := by
  unfold OpenEffect at h
  split at h
  · rw [h.2.2.2.1]
  · obtain ⟨⟨f, -, rfl⟩, -⟩ := h
    split <;> rfl
  · obtain ⟨-, j, b, -, rfl, -⟩ := h
    rfl

/-! ## Locks -/

/-- The fd entry `o` holds no lock (or is no fd). -/
def NoLock (o : Option OsFd) : Prop := ∀ d, o = some d → d.ofd = none ∧ d.flk = none

/-- `st'` has `st`'s descriptions but for some that hold no lock in either (a new fd, unlocked; a
closed one that was unlocked): what every step but the lock calls and `Close` keeps
(`isFsStep_lockFrame`), and so the locks' interpretation (`lockCtx_frame`). -/
def LockFrame (st st' : OsState) : Prop :=
  ∀ fd, st'.proc.fds !! fd = st.proc.fds !! fd ∨
    (NoLock (st.proc.fds !! fd) ∧ NoLock (st'.proc.fds !! fd))

/-- The operations that change a description's locks or remove a description. -/
def LockOp (o : String) : Prop := o = "Flock" ∨ o = "OfdLock" ∨ o = "Close"

theorem lockFrame_refl (st : OsState) : LockFrame st st := fun _ => .inl rfl

theorem lockFrame_trans {st st' st'' : OsState} (h1 : LockFrame st st') (h2 : LockFrame st' st'') :
    LockFrame st st'' := by
  intro fd
  rcases h2 fd with h2 | ⟨h2a, h2b⟩
  · rcases h1 fd with h1 | h1
    · exact .inl (h2.trans h1)
    · rw [h2]; exact .inr h1
  · rcases h1 fd with h1 | ⟨h1a, -⟩
    · exact .inr ⟨h1 ▸ h2a, h2b⟩
    · exact .inr ⟨h1a, h2b⟩

theorem lockFrame_of_fds {st st' : OsState} (h : st'.proc.fds = st.proc.fds) : LockFrame st st' :=
  fun fd => .inl (by rw [h])

/-- A lock call's step leaves the state as it was or sets the description's lock of its kind. -/
theorem lockStep_cases [GooseExts] [GoGlobalContext] {st : OsState} {k : LockKind} {fd : w64}
    {d : OsFd} {req : Option Bool} {nb : Bool} {w e' : Expr} {st' : OsState}
    (h : LockStep st k fd d req nb w e' st') : st' = st ∨ ∃ x, st' = st.setFd fd (d.setLk k x) := by
  unfold LockStep at h
  split at h
  · rcases h with ⟨-, ⟨-, rfl, -⟩ | ⟨e, -, rfl, -⟩ | ⟨-, -, rfl, -⟩⟩
    · exact .inr ⟨_, rfl⟩
    · exact .inl rfl
    · exact .inl rfl
  · rcases h with ⟨rfl, -⟩ | ⟨e, -, -, rfl | rfl⟩
    · exact .inr ⟨_, rfl⟩
    · exact .inl rfl
    · exact .inr ⟨_, rfl⟩

/-- A lock call's step returns an errno, or waits (steps to the call itself, `w`). -/
theorem lockStep_val [GooseExts] [GoGlobalContext] {st : OsState} {k : LockKind} {fd : w64}
    {d : OsFd} {req : Option Bool} {nb : Bool} {w e' : Expr} {st' : OsState}
    (h : LockStep st k fd d req nb w e' st') : (toVal e').isSome ∨ e' = w := by
  unfold LockStep at h
  split at h
  · rcases h with ⟨-, ⟨-, -, rfl⟩ | ⟨e, -, -, rfl⟩ | ⟨-, -, -, rfl⟩⟩
    · exact .inl rfl
    · exact .inl rfl
    · exact .inr rfl
  · rcases h with ⟨-, rfl⟩ | ⟨e, -, rfl, -⟩ <;> exact .inl rfl

theorem setLk_ino (d : OsFd) (k : LockKind) (x : Option Bool) : (d.setLk k x).ino = d.ino := by
  cases k <;> rfl
theorem setLk_readable (d : OsFd) (k : LockKind) (x : Option Bool) :
    (d.setLk k x).readable = d.readable := by cases k <;> rfl
theorem setLk_writable (d : OsFd) (k : LockKind) (x : Option Bool) :
    (d.setLk k x).writable = d.writable := by cases k <;> rfl

section
variable [GooseExts] [GoGlobalContext]

/-- **Every step keeps the committed entries committed.** -/
theorem isFsStep_commitGrows {o : String} {v : val} {st st' : OsState} {e' : Expr}
    (h : IsFsStep o v st e' st') : CommitGrows st st' := by
  intro y hy
  unfold IsFsStep at h
  split at h
  · rcases h with ⟨p, fl, t, start, -, -, -, -, -, hc⟩ | ⟨p, fl, t, start, -, -, -, -, -, hc⟩
    · rcases hc with ⟨st1, tgt, fd, he, -, rfl, -⟩ | ⟨e, -, -, -, rfl | ⟨tgt, he⟩⟩
      · have h1 := openEffect_committed he
        cases tgt <;> (show st1.fs.committed y; rw [h1]; exact hy)
      · exact hy
      · rw [openEffect_committed he]; exact hy
    · rcases hc with ⟨fd, -, rfl, -⟩ | ⟨e, -, rfl, -⟩ <;> exact hy
  all_goals (try simp only [] at h)
  all_goals first
    | (obtain ⟨_, _, _, _, _, -, -, -, hl⟩ := h
       rcases lockStep_cases hl with rfl | ⟨x, rfl⟩ <;> exact hy)
    | (obtain ⟨_, _, _, _, _, -, -, -, -, -, -, hl⟩ := h
       rcases lockStep_cases hl with rfl | ⟨x, rfl⟩ <;> exact hy)
    | skip
  all_goals (grind [OsState.commitAll, openEffect_committed, committed_setFile,
    committed_stampFile, committed_setProc, committed_metaEnd, committed_metaDo, committed_takeIno,
    committed_doneInflight, committed_addInflight, OsState.delOfd])

/-- **Every step keeps the committed entries committed** (`FsStep`). -/
theorem fsStep_commitGrows {o : String} {v : val} {h : GMap Loc (NonAtomic val)} {st st' : OsState}
    {e' : Expr} {h' : GMap Loc (NonAtomic val)} (hs : FsStep o v h st () e' h' st' ()) :
    CommitGrows st st' := by
  rcases hs with hs | ⟨-, -, -, -, -, rfl⟩
  · exact isFsStep_commitGrows hs.1
  · exact commitGrows_refl _

/-- A step is an `IsFsStep`, or `mmap`'s step to itself, which changes nothing (`MmapStall`). -/
theorem fsStep_cases {o : String} {v : val} {h : GMap Loc (NonAtomic val)} {st st' : OsState}
    {e' : Expr} {h' : GMap Loc (NonAtomic val)} (hs : FsStep o v h st () e' h' st' ()) :
    IsFsStep o v st e' st' ∨ st' = st := by
  rcases hs with hs | ⟨-, -, -, -, -, rfl⟩
  · exact .inl hs.1
  · exact .inr rfl

/-- A step of an operation other than `mmap` returns (`FsStepV`). -/
theorem fsStepV_of_ne {o : String} {v : val} {h : GMap Loc (NonAtomic val)} {st st' : OsState}
    {e' : Expr} {h' : GMap Loc (NonAtomic val)} (hM : o ≠ "Mmap")
    (hs : FsStep o v h st () e' h' st' ()) : FsStepV o v h st () e' h' st' () :=
  hs.resolve_right (fun hm => hM hm.1)

end


/-! ## The fds of directories outside the roots' trees -/

/-- No fd of a file or of a tree's directory has the number of an outside directory's fd. -/
def OfdDisj (st : OsState) : Prop :=
  ∀ fd, st.proc.ofds !! fd ≠ none → st.proc.fds !! fd = none ∧ st.proc.dfds !! fd = none

/-- `st'` has `st`'s outside fds, and no fd of a file or of a tree's directory `st` has not. -/
def ProcSub (st st' : OsState) : Prop :=
  st'.proc.ofds = st.proc.ofds ∧ (∀ fd, st'.proc.fds !! fd ≠ none → st.proc.fds !! fd ≠ none) ∧
    (∀ fd, st'.proc.dfds !! fd ≠ none → st.proc.dfds !! fd ≠ none)

theorem procSub_refl (st : OsState) : ProcSub st st := ⟨rfl, fun _ h => h, fun _ h => h⟩

theorem procSub_trans {st st' st'' : OsState} (h1 : ProcSub st st') (h2 : ProcSub st' st'') :
    ProcSub st st'' :=
  ⟨h2.1.trans h1.1, fun fd h => h1.2.1 fd (h2.2.1 fd h), fun fd h => h1.2.2 fd (h2.2.2 fd h)⟩

theorem procSub_of_proc {st st' : OsState} (h : st'.proc = st.proc) : ProcSub st st' := by
  rw [ProcSub, h]; exact ⟨rfl, fun _ h => h, fun _ h => h⟩

theorem ofdDisj_procSub {st st' : OsState} (hd : OfdDisj st) (h : ProcSub st st') : OfdDisj st' := by
  intro fd ho
  rw [h.1] at ho
  obtain ⟨h1, h2⟩ := hd fd ho
  exact ⟨Classical.byContradiction fun hn => h.2.1 fd hn h1,
    Classical.byContradiction fun hn => h.2.2 fd hn h2⟩

theorem procSub_setFile (st : OsState) (i : Ino) (f : OsFile) : ProcSub st (st.setFile i f) :=
  procSub_of_proc rfl
theorem procSub_stampFile (st : OsState) (i : Ino) (g : Nat → OsFile) :
    ProcSub st (st.stampFile i g) := procSub_of_proc rfl
theorem procSub_takeIno (st : OsState) : ProcSub st st.takeIno := procSub_of_proc rfl
theorem procSub_commitAll (st : OsState) : ProcSub st st.commitAll := procSub_of_proc rfl
theorem procSub_metaEnd (st : OsState) (t : Nat) : ProcSub st (st.metaEnd t) :=
  ⟨rfl, fun _ h => h, fun _ h => h⟩
theorem procSub_doneInflight (st : OsState) (t : Nat) : ProcSub st (st.doneInflight t) :=
  ⟨rfl, fun _ h => h, fun _ h => h⟩
theorem procSub_addInflight (st : OsState) (t : Nat) (c : OsChange) :
    ProcSub st (st.addInflight t c) := ⟨rfl, fun _ h => h, fun _ h => h⟩
theorem procSub_metaDo (st : OsState) (o : MetaOp) (s : Nat) : ProcSub st (st.metaDo o s) := by
  refine ⟨rfl, fun _ h => h, fun fd h => ?_⟩
  have h' : (GMap.fmap (·.note o) st.proc.dfds) !! fd ≠ none := h
  rw [GMap.lookup_fmap] at h'
  cases hq : st.proc.dfds !! fd <;> simp_all

theorem procSub_setFd (st : OsState) (fd : w64) (d d0 : OsFd) (h0 : st.proc.fds !! fd = some d0) :
    ProcSub st (st.setFd fd d) := by
  refine ⟨rfl, fun fd' h => ?_, fun _ h => h⟩
  by_cases hq : fd = fd'
  · subst hq; rw [h0]; simp
  · have : (<[fd := d]> st.proc.fds) !! fd' ≠ none := h
    rwa [GMap.lookup_insert_ne _ _ hq] at this

theorem procSub_openEffect {st : OsState} {p : GoString} {acc : Nat} {creat trunc : Bool}
    {start : Nat} {st1 : OsState} {tgt : Node} (h : OpenEffect st p acc creat trunc start st1 tgt) :
    ProcSub st st1 := by
  unfold OpenEffect at h
  split at h
  · rw [h.2.2.2.1]; exact procSub_refl st
  · obtain ⟨⟨f, -, rfl⟩, -⟩ := h
    split
    · exact procSub_stampFile _ _ _
    · exact procSub_refl st
  · obtain ⟨-, j, b, -, rfl, -⟩ := h
    exact procSub_trans (procSub_trans (procSub_setFile _ _ _) (procSub_takeIno _))
      (procSub_metaDo _ _ _)

theorem lockFrame_insert {st st' : OsState} {fd : w64} {d : OsFd}
    (h : st'.proc.fds = <[fd := d]> st.proc.fds) (hfree : st.proc.fds !! fd = none)
    (hd : d.ofd = none ∧ d.flk = none) : LockFrame st st' := by
  intro fd'
  rw [h]
  by_cases hq : fd = fd'
  · subst hq; rw [GMap.lookup_insert, hfree]
    refine .inr ⟨fun d' h' => (by cases h'), fun d' h' => ?_⟩
    cases h'; exact hd
  · rw [GMap.lookup_insert_ne _ _ hq]; exact .inl rfl

section
variable [GooseExts] [GoGlobalContext]

theorem openEffect_fds {st : OsState} {p : GoString} {acc : Nat} {creat trunc : Bool}
    {start : Nat} {st1 : OsState} {tgt : Node} (h : OpenEffect st p acc creat trunc start st1 tgt) :
    st1.proc.fds = st.proc.fds := by
  unfold OpenEffect at h
  split at h
  · rw [h.2.2.2.1]
  · obtain ⟨⟨f, -, rfl⟩, -⟩ := h
    split <;> rfl
  · obtain ⟨-, j, b, -, rfl, -⟩ := h
    rfl

/-- **Every step but the lock calls and `Close` keeps the descriptions, and opens only unlocked
ones.** -/
theorem isFsStep_lockFrame {o : String} {v : val} {st st' : OsState} {e' : Expr}
    (h : IsFsStep o v st e' st') (ho : ¬ LockOp o) : LockFrame st st' := by
  unfold IsFsStep at h
  split at h
  · rcases h with ⟨p, fl, t, start, -, -, -, -, -, hc⟩ | ⟨p, fl, t, start, -, -, -, -, -, hc⟩
    · dsimp only at hc
      rcases hc with ⟨st1, tgt, fd, he, hfree, rfl, -⟩ | ⟨e, -, -, -, rfl | ⟨tgt, he⟩⟩
      · have h1 : st1.proc.fds = st.proc.fds := (openEffect_fds he).trans rfl
        cases tgt with
        | file i =>
          exact lockFrame_insert (d := OsFd.mk i _ _ none none) (by rw [← h1]; rfl) hfree.2.1
            ⟨rfl, rfl⟩
        | dir j => exact lockFrame_of_fds h1
      · exact lockFrame_of_fds rfl
      · exact lockFrame_of_fds ((openEffect_fds he).trans rfl)
    · rcases hc with ⟨fd, -, rfl, -⟩ | ⟨e, -, rfl, -⟩ <;> exact lockFrame_of_fds rfl
  all_goals (try simp only [] at h)
  all_goals first
    | (exfalso; apply ho; simp [LockOp]; done)
    | (apply lockFrame_of_fds
       grind [OsState.setProc, OsState.setFile, OsState.stampFile, OsState.takeIno,
        OsState.metaEnd, OsState.metaDo, OsState.doneInflight, OsState.addInflight,
        OsState.commitAll, OsState.delOfd, OsState.addOfd])

/-- `isFsStep_lockFrame` for any step (`mmap`'s step to itself changes nothing). -/
theorem fsStep_lockFrame {o : String} {v : val} {h : GMap Loc (NonAtomic val)} {st st' : OsState}
    {e' : Expr} {h' : GMap Loc (NonAtomic val)} (hs : FsStep o v h st () e' h' st' ())
    (ho : ¬ LockOp o) : LockFrame st st' := by
  rcases fsStep_cases hs with hs | rfl
  · exact isFsStep_lockFrame hs ho
  · exact fun _ => .inl rfl

end

section
variable [GooseExts] [GoGlobalContext]

/-- **Every step but `OutClose` keeps the outside fds apart from the others, and adds at most a
fresh one.** -/
theorem isFsStep_ofd {o : String} {v : val} {st st' : OsState} {e' : Expr}
    (h : IsFsStep o v st e' st') (ho : o ≠ "OutClose") (hd : OfdDisj st) :
    OfdDisj st' ∧ (st'.proc.ofds = st.proc.ofds ∨
      ∃ fd, FdFree st fd ∧ st'.proc.ofds = <[fd := ()]> st.proc.ofds) := by
  have keep : ProcSub st st' → OfdDisj st' ∧ (st'.proc.ofds = st.proc.ofds ∨
      ∃ fd, FdFree st fd ∧ st'.proc.ofds = <[fd := ()]> st.proc.ofds) :=
    fun hs => ⟨ofdDisj_procSub hd hs, .inl hs.1⟩
  unfold IsFsStep at h
  split at h
  · rcases h with ⟨p, fl, t, start, -, -, -, -, -, hc⟩ | ⟨p, fl, t, start, -, -, -, -, -, hc⟩
    · dsimp only at hc
      rcases hc with ⟨st1, tgt, fd, he, hfree, rfl, -⟩ | ⟨e, -, -, -, rfl | ⟨tgt, he⟩⟩
      · have hs := procSub_trans (procSub_metaEnd st t) (procSub_openEffect he)
        obtain ⟨-, -, -, hon⟩ := hfree
        refine ⟨fun fd' ho' => ?_, .inl ?_⟩
        · cases tgt with
          | file i =>
            have ho1 : st1.proc.ofds !! fd' ≠ none := ho'
            rw [hs.1] at ho1
            have hne : fd' ≠ fd := fun hq => by subst hq; exact ho1 hon
            obtain ⟨h1, h2⟩ := hd fd' ho1
            refine ⟨?_, ?_⟩
            · show (<[fd := _]> st1.proc.fds) !! fd' = none
              rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]
              exact Classical.byContradiction fun hn => hs.2.1 fd' hn h1
            · show st1.proc.dfds !! fd' = none
              exact Classical.byContradiction fun hn => hs.2.2 fd' hn h2
          | dir j =>
            have ho1 : st1.proc.ofds !! fd' ≠ none := ho'
            rw [hs.1] at ho1
            have hne : fd' ≠ fd := fun hq => by subst hq; exact ho1 hon
            obtain ⟨h1, h2⟩ := hd fd' ho1
            refine ⟨?_, ?_⟩
            · show st1.proc.fds !! fd' = none
              exact Classical.byContradiction fun hn => hs.2.1 fd' hn h1
            · show (<[fd := _]> st1.proc.dfds) !! fd' = none
              rw [GMap.lookup_insert_ne _ _ (Ne.symm hne)]
              exact Classical.byContradiction fun hn => hs.2.2 fd' hn h2
        · cases tgt <;> exact hs.1
      · exact keep (procSub_metaEnd st t)
      · exact keep (procSub_trans (procSub_metaEnd st t) (procSub_openEffect he))
    · rcases hc with ⟨fd, hfree, rfl, -⟩ | ⟨e, -, rfl, -⟩
      · obtain ⟨h0, hfn, hdn, hon⟩ := hfree
        refine ⟨fun fd' ho' => ?_, .inr ⟨fd, ⟨h0, hfn, hdn, hon⟩, rfl⟩⟩
        have ho1 : (<[fd := ()]> st.proc.ofds) !! fd' ≠ none := ho'
        by_cases hq : fd = fd'
        · subst hq; exact ⟨hfn, hdn⟩
        · rw [GMap.lookup_insert_ne _ _ hq] at ho1
          exact hd fd' ho1
      · exact keep (procSub_metaEnd st t)
  all_goals (try simp only [] at h)
  all_goals first
    | (obtain ⟨_, _, _, _, _, -, hd, -, hl⟩ := h
       rcases lockStep_cases hl with rfl | ⟨x, rfl⟩
       · exact keep (procSub_refl _)
       · exact keep (procSub_setFd _ _ _ _ hd))
    | (obtain ⟨_, _, _, _, _, -, hd, -, -, -, -, hl⟩ := h
       rcases lockStep_cases hl with rfl | ⟨x, rfl⟩
       · exact keep (procSub_refl _)
       · exact keep (procSub_setFd _ _ _ _ hd))
    | exact absurd rfl ho
    | (apply keep
       grind [procSub_refl, procSub_trans, procSub_setFile, procSub_stampFile, procSub_takeIno,
        procSub_commitAll, procSub_metaEnd, procSub_doneInflight, procSub_addInflight,
        procSub_metaDo, procSub_of_proc, OsState.setProc, ProcSub, GMap.lookup_delete_iff,
        GMap.lookup_insert, GMap.lookup_insert_ne])

end

end Fs
end Perennial

end
