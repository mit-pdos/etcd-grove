/-
What `NoIoErr` and `NoMapLockErr` on one covered path `p` (`FsNoErrAt p`: `FsNoErrOn (· = p)` and
`p` fits) say of the calls `os.RemoveAll`'s model makes on `p` (wal-safe, 2026-11-22, step 2 (D),
design (FNE) of `notes/wal-units/tester.md`: `RemoveAll(dir.tmp)` returns `nil` only with `dir.tmp`
gone): an `unlink` of a file succeeds and one of a directory answers `EISDIR`
(`unlink_noErrAt`); an `rmdir` of an empty directory succeeds and one of a non-empty one answers
`ENOTEMPTY` (`rmdir_noErrAt`); a read-only `open` of a directory succeeds or answers `EINTR`
(`openDir_noErrAt`). Each from the semantics' own step (the one the premise restricts), for
`wp_fs_postSh` (`WpPostShared.lean`). Untrusted.
-/
module

public import GooseLang.Ext.Fs.NoErrSpecsOpenFile
public import GooseLang.Ext.Fs.NoIoErrSpecs
public import GooseLang.Ext.Fs.TreeStepLemmas

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

/-- **The file system does not fail on the path `p`**, which fits. -/
abbrev FsNoErrAt [ExtSemantics fsExt] (p : GoString) : Prop := FsNoErrOn (· = p) ∧ PathFits p

section step
variable [GooseExts] [GoGlobalContext] [go.BasicIntoValInj] [S : ExtSemantics fsExt] [FsSemOk]

/-- **`unlink(2)` of a covered `d/b`**: of a file, errno 0; of a directory, `EISDIR`. -/
theorem unlink_noErrAt {d b : GoString} {j : Ino} {k : Nat} (hne : FsNoErrAt (child d b))
    {h : GMap Loc (NonAtomic val)} {st : OsState} {g : Unit} {e' : Expr}
    {h' : GMap Loc (NonAtomic val)} {st' : OsState} {g' : Unit}
    (hd : st.lookup d = some (.dir j)) (hb : NameOk b) (hw : FsTreeWf st)
    (hs : S.step "Unlink" (PairV (osTokV k) (#(child d b))) h st g e' h' st' g') :
    ((∃ i, st.tree.entry j b = some (.file i)) → e' = Val (#(0 : w64))) ∧
    ((∃ J, st.tree.entry j b = some (.dir J)) → e' = Val (#EISDIR)) := by
  obtain ⟨⟨Sio, -, h1, -, hp⟩, hfit⟩ := hne
  have hst := (fsStepV_of_ne (by decide) (FsSemOk.step_sub _ _ _ _ _ _ _ _ _ hs)).1
  have hcov : IoCovers Sio "Unlink" (PairV (osTokV k) (#(child d b))) st :=
    ⟨k, child d b, rfl, hp _ rfl, hfit⟩
  have hl : st.lookup (child d b) = st.tree.entry j b := lookup_child hw.roots hd hb
  obtain ⟨p', k', s0, hv, htn, hcall, -⟩ := hst
  obtain ⟨rfl, rfl⟩ := tokPath_inj hv
  constructor
  · rintro ⟨i, hi⟩
    have hz := noIoErr_step (Sio := Sio) hs hcov
      ⟨_, ((st.metaEnd k).metaDo (.remove j b (.file i)) s0), ⟨child d b, k, s0, rfl, htn, hcall,
        .inl ⟨i, j, b, by rw [hl, hi], parent_child hd hb, .inl ⟨rfl, rfl⟩⟩⟩, rfl⟩
    exact hz
  · rintro ⟨J, hJ⟩
    have hno : ¬ ∃ e'' st'', IsFsStep "Unlink" (PairV (osTokV k) (#(child d b))) st e'' st'' ∧
        ErrnoZero "Unlink" e'' := by
      rintro ⟨e'', st'', ⟨p2, k2, s2, hv2, -, -, hr⟩, hz⟩
      obtain ⟨rfl, rfl⟩ := tokPath_inj hv2
      simp only [ErrnoZero] at hz
      rcases hr with ⟨i, -, -, hli, -⟩ | ⟨e, he, rfl, -⟩
      · rw [hl, hJ] at hli; cases hli
      · injection hz with hz; exact he (go.intoVal_inj hz)
    obtain ⟨k3, p3, hv3, -, hdir⟩ := noIoErr_pathErrno (Sio := Sio) hs hcov hno
    obtain ⟨rfl, rfl⟩ := tokPath_inj hv3
    exact hdir ⟨J, by rw [hl, hJ]⟩

/-- **`rmdir(2)` of a covered `d/b`, a directory `J`**: empty, errno 0; with an entry, `ENOTEMPTY`. -/
theorem rmdir_noErrAt {d b : GoString} {j J : Ino} {k : Nat} (hne : FsNoErrAt (child d b))
    {h : GMap Loc (NonAtomic val)} {st : OsState} {g : Unit} {e' : Expr}
    {h' : GMap Loc (NonAtomic val)} {st' : OsState} {g' : Unit}
    (hd : st.lookup d = some (.dir j)) (hb : NameOk b) (hw : FsTreeWf st)
    (hJ : st.tree.entry j b = some (.dir J))
    (hs : S.step "Rmdir" (PairV (osTokV k) (#(child d b))) h st g e' h' st' g') :
    ((∀ c, st.tree.entry J c = none) → e' = Val (#(0 : w64))) ∧
    ((∃ c n, st.tree.entry J c = some n) → e' = Val (#ENOTEMPTY)) := by
  obtain ⟨⟨Sio, -, h1, -, hp⟩, hfit⟩ := hne
  have hst := (fsStepV_of_ne (by decide) (FsSemOk.step_sub _ _ _ _ _ _ _ _ _ hs)).1
  have hcov : IoCovers Sio "Rmdir" (PairV (osTokV k) (#(child d b))) st :=
    ⟨k, child d b, rfl, hp _ rfl, hfit⟩
  have hl : st.lookup (child d b) = some (.dir J) := by rw [lookup_child hw.roots hd hb, hJ]
  obtain ⟨p', k', s0, hv, htn, hcall, -⟩ := hst
  obtain ⟨rfl, rfl⟩ := tokPath_inj hv
  constructor
  · intro hemp
    exact noIoErr_step (Sio := Sio) hs hcov
      ⟨_, ((st.metaEnd k).metaDo (.remove j b (.dir J)) s0), ⟨child d b, k, s0, rfl, htn, hcall,
        .inl ⟨J, j, b, ⟨hl, hemp⟩, parent_child hd hb, .inl ⟨rfl, rfl⟩⟩⟩, rfl⟩
  · rintro ⟨c, n, hc⟩
    have hno : ¬ ∃ e'' st'', IsFsStep "Rmdir" (PairV (osTokV k) (#(child d b))) st e'' st'' ∧
        ErrnoZero "Rmdir" e'' := by
      rintro ⟨e'', st'', ⟨p2, k2, s2, hv2, -, -, hr⟩, hz⟩
      obtain ⟨rfl, rfl⟩ := tokPath_inj hv2
      simp only [ErrnoZero] at hz
      rcases hr with ⟨J', -, -, ⟨hli, hemp⟩, -⟩ | ⟨e, he, rfl, -⟩
      · rw [hl] at hli; cases hli
        rw [hemp c] at hc; cases hc
      · injection hz with hz; exact he (go.intoVal_inj hz)
    obtain ⟨k3, p3, hv3, -, hne'⟩ := noIoErr_pathErrno (Sio := Sio) hs hcov hno
    obtain ⟨rfl, rfl⟩ := tokPath_inj hv3
    exact hne' ⟨J, c, n, hl, hc⟩

/-- **A read-only `open(2)` (`O_CLOEXEC`) of a covered directory**: errno 0 or `EINTR`. -/
theorem openDir_noErrAt {p : GoString} {J : Ino} {k : Nat} (hne : FsNoErrAt p)
    {h : GMap Loc (NonAtomic val)} {st : OsState} {g : Unit} {e' : Expr}
    {h' : GMap Loc (NonAtomic val)} {st' : OsState} {g' : Unit}
    (hl : st.lookup p = some (.dir J))
    (hs : S.step "Open" (PairV (osTokV k) (PairV (#p) (#(W64 0x80000)))) h st g e' h' st' g') :
    ∀ fd e : w64, e' = osRes (#fd) e → e = 0 ∨ e = EINTR := by
  obtain ⟨⟨Sio, -, h1, h2, hp⟩, hfit⟩ := hne
  have hst := (fsStepV_of_ne (by decide) (FsSemOk.step_sub _ _ _ _ _ _ _ _ _ hs)).1
  intro fd e he
  by_cases he0 : e = 0
  · exact .inl he0
  refine .inr (open_failure_eintr (Sio := Sio) ⟨hp _ rfl, hfit⟩ ?_ hst hs fd e he he0)
  intro fd' hfree
  have htp := treePath_of_lookup hl
  rcases hst with ⟨p', fl, t, s0, hv, -, hfl, hcall, -⟩ | ⟨p', fl, t, s0, hv, hntp, -⟩
  · injection hv with hv1 hv2
    injection hv2 with hv2 hv3
    have hk : t = k := by injection hv1 with hv1; exact (extVal_inj hv1).symm
    have hp' : p' = p := (go.intoVal_inj hv2).symm
    have hfl' : fl = W64 0x80000 := (go.intoVal_inj hv3).symm
    subst hk hp' hfl'
    refine ⟨_, .inl ⟨p', W64 0x80000, t, s0, rfl, htp, hfl, hcall, ⟨fun h0 => absurd h0 (by decide),
      .inl ⟨st.metaEnd t, .dir J, fd', ?_, hfree, rfl, rfl⟩⟩⟩⟩
    unfold OpenEffect
    have hl0 : (st.metaEnd t).lookup p' = some (.dir J) := hl
    rw [hl0]
    exact ⟨by decide, by decide, by decide, rfl, rfl⟩
  · injection hv with hv1 hv2
    injection hv2 with hv2 hv3
    have hp' : p' = p := (go.intoVal_inj hv2).symm
    subst hp'
    exact absurd htp hntp

end step

end Fs
end Perennial

end
