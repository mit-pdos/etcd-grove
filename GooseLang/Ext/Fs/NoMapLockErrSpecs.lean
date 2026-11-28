/-
What the program logic may use of the premises **no error of `flock`, `mmap`, `munmap`**
(`NoMapLockErr S`, pending the user's review) and **no I/O error** (`NoIoErr S`) on the calls bbolt's
`Open` and `Close` make on the database file: `munmap` returns 0, a non-blocking `flock` 0 or
`EAGAIN` and `LOCK_UN` 0, `mmap` no errno (a mapping, or no return with no room for it, `MmapStall`), a
file's `close` 0 (`NoIoErr`), and the error-free specs of `munmap`, `flock` and `close` derived from their
specs by `wp_ext_post`, and of `mmap` from `wp_osMmapG`. Every inode covered
(`hS`), as `NoIoErrSpecs.lean`'s. Untrusted.
-/
module

public import GooseLang.Ext.Fs.NoMapLockErr
public import GooseLang.Ext.Fs.NoIoErrSpecs
public import GooseLang.Ext.Fs.Locks

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section step
variable [GooseExts] [GoGlobalContext] [go.BasicIntoValInj] [S : ExtSemantics fsExt] [FsSemOk]
variable {tf : GoTypeFns}

/-- **A covered lock or mapping call ends `MapLockOk` when it can** (`NoMapLockErr`, from the
semantics' step). -/
theorem noMapLockErr_step {Sio : IoSet} [hsat : FsStepSat (NoMapLockErr Sio)] {o : String}
    {v : val} {h : GMap Loc (NonAtomic val)} {st : OsState} {g : Unit} {e' : Expr}
    {h' : GMap Loc (NonAtomic val)} {st' : OsState} {g' : Unit}
    (hs : S.step tf o v h st g e' h' st' g') (hc : MapLockCovers Sio o v st)
    (hex : ∃ e'' st'', IsFsStep o v st e'' st'' ∧ MapLockOk o v e'') : MapLockOk o v e' :=
  hsat.sat o v h st g e' h' st' g' hs hc hex

/-- Every step of `munmap` returns 0 when every inode is covered. -/
theorem munmap_noErr {Sio : IoSet} [FsStepSat (NoMapLockErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (v : val) :
    ∀ h st g e' h' st' g', S.step tf "Munmap" v h st g e' h' st' g' →
      ∃ r, e' = Val r ∧ r = #(0 : w64) := by
  intro h st g e' h' st' g' hs
  have hf := fsStepV_of_ne (by decide) (FsSemOk.step_sub _ _ _ _ _ _ _ _ _ hs)
  obtain ⟨hst, -, -⟩ := hf
  simp only [IsFsStep] at hst
  obtain ⟨base, len, cap, m, hv, hm, hlen, hcap, -⟩ := hst
  have hz := noMapLockErr_step (Sio := Sio) hs
    (by simp only [MapLockCovers]; exact ⟨base, _, m, hv, hm, hS _ _⟩)
    ⟨Val (#(0 : w64)), st.setProc { st.proc with
        maps := GMap.delete base st.proc.maps, mapDesc := GMap.delete base st.proc.mapDesc },
      by simp only [IsFsStep]; refine ⟨base, len, cap, m, hv, hm, hlen, hcap, .inl ⟨?_, ?_⟩⟩ <;> trivial,
      (rfl : Val (#(0 : w64)) = Val (#(0 : w64)))⟩
  exact ⟨_, (hz : e' = Val (#(0 : w64))), rfl⟩

/-- Every step of `flock(fd, how)` that unlocks, or is non-blocking, returns 0 or (only a
non-blocking lock request) `EAGAIN`, when every inode is covered. -/
theorem flock_noErr {Sio : IoSet} [FsStepSat (NoMapLockErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (fd how : w64) (req : Option Bool) (nb : Bool) (hhow : flockReq how.toNat = some (req, nb))
    (hk : req = none ∨ nb = true) :
    ∀ h st g e' h' st' g', S.step tf "Flock" (PairV (#fd) (#how)) h st g e' h' st' g' →
      ∃ r, e' = Val r ∧ (r = #(0 : w64) ∨ (req ≠ none ∧ r = #EAGAIN)) := by
  intro h st g e' h' st' g' hs
  have hf := fsStepV_of_ne (by decide) (FsSemOk.step_sub _ _ _ _ _ _ _ _ _ hs)
  obtain ⟨hst, -, -⟩ := hf
  simp only [IsFsStep] at hst
  obtain ⟨fd', how', d, req', nb', hv, hfd, hhow', hl⟩ := hst
  have hv' := hv
  injection hv' with h1 h2
  cases go.intoVal_inj h1; cases go.intoVal_inj h2
  rw [hhow, Option.some.injEq, Prod.mk.injEq] at hhow'; obtain ⟨rfl, rfl⟩ := hhow'
  -- an outcome `MapLockOk` exists
  have hex : ∃ e'' st'', IsFsStep "Flock" (PairV (#fd) (#how)) st e'' st'' ∧
      MapLockOk "Flock" (PairV (#fd) (#how)) e'' := by
    rcases req with _ | ex
    · refine ⟨Val (#(0 : w64)), st.setFd fd (d.setLk .flock none), ?_, Or.inl rfl⟩
      simp only [IsFsStep]
      exact ⟨fd, how, d, none, nb, rfl, hfd, hhow, .inl ⟨rfl, rfl⟩⟩
    · unfold LockStep at hl
      obtain ⟨hfree, -⟩ := hl
      by_cases hc : LockConflict st .flock fd d.ino ex
      · rcases hk with hk | hk
        · cases hk
        subst hk
        refine ⟨Val (#EAGAIN), st, ?_, Or.inr (Or.inl ⟨fd, how, ex, rfl, ?_, rfl⟩)⟩
        · simp only [IsFsStep]
          exact ⟨fd, how, d, some ex, true, rfl, hfd, hhow, hfree,
            .inr (.inl ⟨EAGAIN, by decide, rfl, rfl⟩)⟩
        · exact hhow
      · refine ⟨Val (#(0 : w64)), st.setFd fd (d.setLk .flock (some ex)), ?_, Or.inl rfl⟩
        simp only [IsFsStep]
        exact ⟨fd, how, d, some ex, nb, rfl, hfd, hhow, hfree, .inl ⟨hc, rfl, rfl⟩⟩
  have hz := noMapLockErr_step (Sio := Sio) hs
    (by simp only [MapLockCovers]; exact ⟨fd, how, d, rfl, hfd, hS _ _⟩) hex
  rcases (hz : e' = Val (#(0 : w64)) ∨ (∃ (fd1 how1 : w64) (ex : Bool),
      PairV (#fd) (#how) = PairV (#fd1) (#how1) ∧ flockReq how1.toNat = some (some ex, true) ∧
      e' = Val (#EAGAIN)) ∨ e' = ExternalOp fsExt.name "Flock" (Val (PairV (#fd) (#how))))
      with hz | ⟨fd1, how1, ex, hv1, hreq, hz⟩ | hz
  · exact ⟨_, hz, Or.inl rfl⟩
  rotate_left
  · -- the wait: only a blocking lock request's, excluded by `hk`
    exfalso
    subst hz
    unfold LockStep at hl
    rcases req with _ | ex
    · rcases hl with ⟨-, h⟩ | ⟨e, -, h, -⟩ <;> cases h
    · rcases hl with ⟨-, ⟨-, -, h⟩ | ⟨e, -, -, h⟩ | ⟨hnb, -⟩⟩
      · cases h
      · cases h
      · rcases hk with hk | hk
        · cases hk
        · rw [hk] at hnb; cases hnb
  · refine ⟨_, hz, Or.inr ⟨?_, rfl⟩⟩
    injection hv1 with h1 h2
    cases go.intoVal_inj h2
    rw [hhow] at hreq
    intro hn; subst hn
    simp at hreq

/-- A page-aligned base for a new mapping, positive and no mapping's (what `IsFsStep`'s success of
`mmap` needs of it, but for the heap). -/
theorem exists_map_base (M : GMap Loc OsMap) :
    ∃ base : Loc, 0 < base.addr ∧ (osPageSize : Int) ∣ base.addr ∧ M !! base = none := by
  obtain ⟨L, hL⟩ := M.finite
  have hp := freshLoc_pos L
  refine ⟨⟨(osPageSize : Int) * (freshLoc L).addr⟩, ?_, ⟨_, rfl⟩, ?_⟩
  · simp only [osPageSize]; omega
  · cases hb : M.lookup ⟨(osPageSize : Int) * (freshLoc L).addr⟩ with
    | none => rfl
    | some x =>
      have hm := hL _ (by rw [hb]; rfl)
      have := freshLoc_gt L _ hm
      simp only [osPageSize] at this; omega

/-- **No step of a covered `mmap` fails** (`NoMapLockErr`, every inode covered): a step of `mmap`
with the arguments it accepts, from a state where `fd` is open as `d`, never ends in an errno
(the semantics' success exists, `exists_map_base`; the step either returns a mapping or does not
return, `MmapStall`). -/
theorem mmap_noFail {Sio : IoSet} [FsStepSat (NoMapLockErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (fd off len prot fl : w64) (d : OsFd) (hrd : d.readable = true) (hoff : off = 0)
    (hlen : 0 < len.toInt) (hprot : prot.toNat = PROT_READ)
    (hfl : fl.toNat = MAP_SHARED ∨ fl.toNat = MAP_SHARED + MAP_POPULATE) :
    ∀ h st e h' st', st.proc.fds !! fd = some d →
      S.step tf "Mmap" (PairV (#fd) (PairV (#off) (PairV (#len) (PairV (#prot) (#fl))))) h st ()
        (osRes (#null) e) h' st' () → e ≠ 0 → False := by
  intro h st e h' st' hfd hs he
  obtain ⟨base, hpos, hal, hnone⟩ := exists_map_base st.proc.maps
  have hz := noMapLockErr_step (Sio := Sio) hs
    (by simp only [MapLockCovers]; exact ⟨fd, _, d, rfl, hfd, hS _ _⟩)
    ⟨osRes (#base) 0, _, by
      simp only [IsFsStep]
      exact ⟨fd, off, len, prot, fl, d, rfl, hfd, hrd, hoff, hlen, hprot, hfl,
        .inl ⟨base, hpos, hal, hnone, rfl, rfl⟩⟩, Or.inl ⟨_, rfl⟩⟩
  rcases (hz : (∃ r : val, osRes (#null) e = osRes r 0) ∨
      osRes (#null) e = ExternalOp fsExt.name "Mmap" (Val _)) with ⟨r, hr⟩ | hr
  · injection hr with hr
    injection hr with h1 h2
    exact he (go.intoVal_inj h2)
  · cases hr

/-- Every step of a file's `close(fd)` returns 0 when every inode is covered (`NoIoErr`). -/
theorem close_noErr {Sio : IoSet} [FsStepSat (NoIoErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (fd : w64) :
    ∀ h st g e' h' st' g', S.step tf "Close" (#fd) h st g e' h' st' g' →
      ∃ r, e' = Val r ∧ r = #(0 : w64) := by
  intro h st g e' h' st' g' hs
  have hf := fsStepV_of_ne (by decide) (FsSemOk.step_sub _ _ _ _ _ _ _ _ _ hs)
  obtain ⟨hst, -, -⟩ := hf
  simp only [IsFsStep] at hst
  obtain ⟨fd', e, d, hv, hfd, -, -⟩ := hst
  have hz := noIoErr_step (Sio := Sio) hs (by simp only [IoCovers]; exact ⟨fd', d, hv, hfd, hS _ _⟩)
    ⟨Val (#(0 : w64)), st.setProc { st.proc with
        fds := GMap.delete fd' st.proc.fds, mapDesc := GMap.fmap (MapDesc.close fd' d) st.proc.mapDesc },
      by simp only [IsFsStep]; exact ⟨fd', 0, d, hv, hfd, rfl, rfl⟩,
      (rfl : Val (#(0 : w64)) = Val (#(0 : w64)))⟩
  exact ⟨_, (hz : e' = Val (#(0 : w64))), rfl⟩

/-- **Every step of a blocking OFD lock call returns 0 or waits** (`F_OFD_SETLKW`; `NoIoErr`, every
inode covered): its success when there is no conflict, its wait when there is one (`LockStep`), so
`NoIoErr` keeps only those. -/
theorem ofdLockW_noErr {Sio : IoSet} [FsStepSat (NoIoErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (fd typ : w64) :
    ∀ h st e' h' st', S.step tf "OfdLock" (PairV (#fd) (PairV (#(W64 38)) (#typ))) h st () e' h' st' () →
      e' = Val (#(0 : w64)) ∨ ∃ w : val, e' = ExternalOp fsExt.name "OfdLock" (Val w) := by
  intro h st e' h' st' hs
  have hf := fsStepV_of_ne (by decide) (FsSemOk.step_sub _ _ _ _ _ _ _ _ _ hs)
  obtain ⟨hst, -, -⟩ := hf
  simp only [IsFsStep] at hst
  obtain ⟨fd', cmd', typ', d, req, hv, hfd, hcmd, hreq, hw, hr, hl⟩ := hst
  have hv' := hv
  injection hv' with h1 h2; injection h2 with h3 h4
  cases go.intoVal_inj h1; cases go.intoVal_inj h3; cases go.intoVal_inj h4
  have hnb : decide ((W64 38).toNat = F_OFD_SETLK) = false := by decide
  have hex : ∃ e'' st'', IsFsStep "OfdLock" (PairV (#fd) (PairV (#(W64 38)) (#typ))) st e'' st'' ∧
      ErrnoZero "OfdLock" e'' := by
    rcases req with _ | ex
    · refine ⟨Val (#(0 : w64)), st.setFd fd (d.setLk .ofd none), ?_, Or.inl rfl⟩
      simp only [IsFsStep]
      exact ⟨fd, W64 38, typ, d, none, rfl, hfd, hcmd, hreq, hw, hr, .inl ⟨rfl, rfl⟩⟩
    · have hfree := hl.1
      by_cases hc : LockConflict st .ofd fd d.ino ex
      · refine ⟨ExternalOp fsExt.name "OfdLock" (Val (PairV (#fd) (PairV (#(W64 38)) (#typ)))), st, ?_,
          Or.inr ⟨_, rfl⟩⟩
        simp only [IsFsStep]
        refine ⟨fd, W64 38, typ, d, some ex, rfl, hfd, hcmd, hreq, hw, hr, ?_⟩
        rw [hnb]
        exact ⟨hfree, .inr (.inr ⟨rfl, hc, rfl, rfl⟩)⟩
      · refine ⟨Val (#(0 : w64)), st.setFd fd (d.setLk .ofd (some ex)), ?_, Or.inl rfl⟩
        simp only [IsFsStep]
        exact ⟨fd, W64 38, typ, d, some ex, rfl, hfd, hcmd, hreq, hw, hr, ⟨hfree, .inl ⟨hc, rfl, rfl⟩⟩⟩
  exact (noIoErr_step (Sio := Sio) hs
    (by simp only [IoCovers]; exact ⟨fd, W64 38, typ, d, rfl, hfd, hS _ _, by decide⟩) hex :
    e' = Val (#(0 : w64)) ∨ ∃ w : val, e' = ExternalOp fsExt.name "OfdLock" (Val w))

/-- **Every step of a blocking `flock` lock request returns 0 or waits** (`NoMapLockErr`, every inode
covered), as `ofdLockW_noErr`. -/
theorem flockW_noErr {Sio : IoSet} [FsStepSat (NoMapLockErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (fd how : w64) (ex : Bool) (hhow : flockReq how.toNat = some (some ex, false)) :
    ∀ h st e' h' st', S.step tf "Flock" (PairV (#fd) (#how)) h st () e' h' st' () →
      e' = Val (#(0 : w64)) ∨ e' = ExternalOp fsExt.name "Flock" (Val (PairV (#fd) (#how))) := by
  intro h st e' h' st' hs
  have hf := fsStepV_of_ne (by decide) (FsSemOk.step_sub _ _ _ _ _ _ _ _ _ hs)
  obtain ⟨hst, -, -⟩ := hf
  simp only [IsFsStep] at hst
  obtain ⟨fd', how', d, req', nb', hv, hfd, hhow', hl⟩ := hst
  have hv' := hv
  injection hv' with h1 h2
  cases go.intoVal_inj h1; cases go.intoVal_inj h2
  rw [hhow, Option.some.injEq, Prod.mk.injEq] at hhow'; obtain ⟨rfl, rfl⟩ := hhow'
  have hfree := hl.1
  have hex : ∃ e'' st'', IsFsStep "Flock" (PairV (#fd) (#how)) st e'' st'' ∧
      MapLockOk "Flock" (PairV (#fd) (#how)) e'' := by
    by_cases hc : LockConflict st .flock fd d.ino ex
    · refine ⟨ExternalOp fsExt.name "Flock" (Val (PairV (#fd) (#how))), st, ?_, Or.inr (Or.inr rfl)⟩
      simp only [IsFsStep]
      exact ⟨fd, how, d, some ex, false, rfl, hfd, hhow, hfree, .inr (.inr ⟨rfl, hc, rfl, rfl⟩)⟩
    · refine ⟨Val (#(0 : w64)), st.setFd fd (d.setLk .flock (some ex)), ?_, Or.inl rfl⟩
      simp only [IsFsStep]
      exact ⟨fd, how, d, some ex, false, rfl, hfd, hhow, hfree, .inl ⟨hc, rfl, rfl⟩⟩
  have hz := noMapLockErr_step (Sio := Sio) hs
    (by simp only [MapLockCovers]; exact ⟨fd, how, d, rfl, hfd, hS _ _⟩) hex
  rcases (hz : e' = Val (#(0 : w64)) ∨ (∃ (fd1 how1 : w64) (ex : Bool),
      PairV (#fd) (#how) = PairV (#fd1) (#how1) ∧ flockReq how1.toNat = some (some ex, true) ∧
      e' = Val (#EAGAIN)) ∨ e' = ExternalOp fsExt.name "Flock" (Val (PairV (#fd) (#how))))
      with hz | ⟨fd1, how1, ex1, hv1, hreq, -⟩ | hz
  · exact .inl hz
  · injection hv1 with h1 h2
    cases go.intoVal_inj h2
    rw [hhow] at hreq
    simp at hreq
  · exact .inr hz

end step

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **`munmap` with no error** (`wp_osMunmap` under `NoMapLockErr`, every inode covered): the
mapping and its cells gone. -/
theorem wp_osMunmapNE {Sio : IoSet} [FsStepSat (NoMapLockErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (base : Loc) (len cap : w64) (p : Ino) (m : OsMeta) (n : Nat)
    (vf : Nat → val) (hE : ↑osN ⊆ E) (hb : m.maps !! base = some n) (hlen : len.toNat = n)
    (hcap : cap.toNat = n) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osMeta (L := L) p (DFrac.own 1) (m) -∗ cellsR base 0 n vf -∗
      (osMeta (L := L) p (DFrac.own 1) ({ m with maps := GMap.delete base m.maps }) -∗
        Φ (#(0 : w64))) -∗
      WP (ExternalOp fsExt.name "Munmap" (Val (PairV (#base) (PairV (#len) (#cap))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv Hm Hc HΦ
  iapply wp_ext_post "Munmap" _ (by simp [val.isPanic]) (· = #(0 : w64)) (munmap_noErr hS _) Φ
  iapply wp_osMunmap base len cap p m n vf hE hb hlen hcap _ $$ Hinv Hm Hc
  iintro %e Hr %he
  have he0 : e = 0 := go.intoVal_inj he
  subst he0
  icases Hr with (⟨-, Hm⟩ | ⟨%h0, -⟩)
  · iapply HΦ $$ Hm
  · exact absurd rfl h0

/-- **`flock` with no error** (`wp_osFlock` under `NoMapLockErr`, every inode covered), of an unlock
or a non-blocking request: errno 0, or `EAGAIN` for a lock request (a conflict). -/
theorem wp_osFlockNE {Sio : IoSet} [FsStepSat (NoMapLockErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (fd how : w64) (d : OsFd) (req : Option Bool) (nb : Bool) (hE : ↑osN ⊆ E)
    (hhow : flockReq how.toNat = some (req, nb)) (hfree : req ≠ none → d.flk = none)
    (hk : req = none ∨ nb = true) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd (DFrac.own 1) d -∗ lockTok (L := L) .flock fd d -∗
      (∀ e : w64, ⌜e = 0 ∨ (req ≠ none ∧ e = EAGAIN)⌝ -∗ lockOut (L := L) .flock fd d req e -∗
        Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Flock" (Val (PairV (#fd) (#how)))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Ht HΦ
  iapply wp_ext_post "Flock" _ (by simp [val.isPanic])
    (fun r => r = #(0 : w64) ∨ (req ≠ none ∧ r = #EAGAIN)) (flock_noErr hS fd how req nb hhow hk) Φ
  iapply wp_osFlock fd how d req nb hE hhow hfree _ $$ Hinv Hfd Ht
  iintro %e Hout %he
  ihave Hp : (⌜e = 0 ∨ (req ≠ none ∧ e = EAGAIN)⌝ : IProp GF) $$ []
  · ipureintro
    rcases he with he | ⟨hr, he⟩
    · exact Or.inl (go.intoVal_inj he)
    · exact Or.inr ⟨hr, go.intoVal_inj he⟩
  iapply HΦ $$ Hp Hout

/-- **A file's `close(fd)` with no error** (`wp_osClose` under `NoIoErr`, every inode covered). -/
theorem wp_osCloseNE {Sio : IoSet} [FsStepSat (NoIoErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (fd : w64) (d : OsFd) (hE : ↑osN ⊆ E) :
    {{ osInv (L := L) ∗ osFd (L := L) fd (DFrac.own 1) d ∗ lockToks (L := L) fd d }}
      (ExternalOp fsExt.name "Close" (Val (#fd))) @ s; E
    {{ RET #(0 : w64); True }} := by
  iintro %Φ ⟨#Hinv, Hfd, Ht⟩ HΦ
  iapply wp_ext_post "Close" (#fd) (by simp) (· = #(0 : w64)) (close_noErr hS fd) Φ
  iapply wp_osClose fd d hE $$ [Hinv Hfd Ht]
  · iframe; iexact Hinv
  inext
  iintro %e - %he
  rw [he]
  iapply HΦ
  itrivial

/-- **`mmap` with no error** (`wp_osMmapG` under `NoMapLockErr`, every inode covered): fresh cells
at `base`, whose client halves hold the file's bytes, then holes past its end, inside the address
space, and the mapping in the `OsMeta`. With no room for the mapping, the call does not return
(`MmapStall`); it never fails. -/
theorem wp_osMmapNE {Sio : IoSet} [FsStepSat (NoMapLockErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (fd off len prot fl : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (hE : ↑osN ⊆ E)
    (hrd : d.readable = true) (hoff : off = 0) (hlen : 0 < len.toInt)
    (hprot : prot.toNat = PROT_READ)
    (hfl : fl.toNat = MAP_SHARED ∨ fl.toNat = MAP_SHARED + MAP_POPULATE) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino (DFrac.own 1) (m) -∗
      (∀ base : Loc,
        ⌜0 < base.addr ∧ base.addr + len.toNat ≤ maxAddr⌝ -∗
          osMeta (L := L) d.ino (DFrac.own 1) ({ m with maps := <[base := len.toNat]> m.maps }) -∗
          (∃ bs : List w8, ⌜bs.length = m.size⌝ ∗
            cellsR base 0 len.toNat (fun i => toCellVal bs[i]?)) -∗
        osFd (L := L) fd dq d -∗ Φ (PairV (#base) (#(0 : w64)))) -∗
      WP (ExternalOp fsExt.name "Mmap"
        (Val (PairV (#fd) (PairV (#off) (PairV (#len) (PairV (#prot) (#fl))))))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Hm HΦ
  iapply wp_osMmapG fd off len prot fl dq d m (E \ ↑osN) hE hrd hoff hlen hprot hfl (fun _ => False)
    (mmap_noFail hS fd off len prot fl d hrd hoff hlen hprot hfl)
    (osMeta (L := L) d.ino (DFrac.own 1) m)
    (fun base e => mmapRes (L := L) (fun _ => False) d len m (some (base, e))) Φ $$ Hinv [] [HΦ]
    Hfd Hm
  · imodintro
    iintro Hm
    imodintro
    iframe Hm
    iintro %r Hr
    imodintro
    rcases r with _ | ⟨base, e⟩
    · unfold mmapRes mmapPost; iexact Hr
    · unfold mmapPost; iexact Hr
  · iintro %base %e Hr Hfd
    unfold mmapRes
    icases Hr with (⟨%he, Hm, Hc⟩ | ⟨%he, -⟩)
    · obtain ⟨rfl, hpos, hmax⟩ := he
      iapply HΦ $$ %base [] Hm Hc Hfd
      ipureintro; exact ⟨hpos, hmax⟩
    · exact he.2.2.elim

/-- **A blocking OFD lock call, its error witnessed** (`wp_osOfdLock`, wal-fsfix2): with
`F_OFD_SETLKW`, an errno only when the file system can fail on every file (`¬ FsNoErrIno`: under
`NoIoErr` a covered blocking request ends with errno 0 or waits, `ofdLockW_noErr`). -/
theorem wp_osOfdLockW (fd cmd typ : w64) (d : OsFd) (req : Option Bool) (hE : ↑osN ⊆ E)
    (hcmd : cmd.toNat = F_OFD_SETLK ∨ cmd.toNat = F_OFD_SETLKW) (hreq : ofdReq typ.toNat = some req)
    (hw : req = some true → d.writable = true) (hr : req = some false → d.readable = true)
    (hfree : req ≠ none → d.ofd = none) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd (DFrac.own 1) d -∗ lockTok (L := L) .ofd fd d -∗
      (∀ e : w64, ⌜cmd = W64 38 → e ≠ 0 → ¬ FsNoErrIno⌝ -∗ lockOut (L := L) .ofd fd d req e -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "OfdLock" (Val (PairV (#fd) (PairV (#cmd) (#typ))))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Ht HΦ
  by_cases hW : FsNoErrIno ∧ cmd = W64 38
  · obtain ⟨⟨Sio, hi, h1, -, -⟩, rfl⟩ := hW
    haveI := h1
    iapply wp_osOfdLockP fd (W64 38) typ d req hE hcmd hreq hw hr hfree _ (ofdLockW_noErr hi fd typ) Φ
      $$ Hinv Hfd Ht
    iintro %e %he Ho
    iapply HΦ $$ [] Ho
    ipureintro
    intro _ hne
    rcases he with he | ⟨w, he⟩
    · injection he with he; exact absurd (go.intoVal_inj he) hne
    · cases he
  · iapply wp_osOfdLock fd cmd typ d req hE hcmd hreq hw hr hfree Φ $$ Hinv Hfd Ht
    iintro %e Ho
    iapply HΦ $$ [] Ho
    ipureintro
    intro hc _ hn
    exact hW ⟨hn, hc⟩

/-- **A blocking `flock` lock request, its error witnessed** (`wp_osFlock`, wal-fsfix2): an errno
only when the file system can fail on every file (`flockW_noErr`). -/
theorem wp_osFlockW (fd how : w64) (d : OsFd) (ex : Bool) (hE : ↑osN ⊆ E)
    (hhow : flockReq how.toNat = some (some ex, false)) (hfree : d.flk = none) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd (DFrac.own 1) d -∗ lockTok (L := L) .flock fd d -∗
      (∀ e : w64, ⌜e ≠ 0 → ¬ FsNoErrIno⌝ -∗ lockOut (L := L) .flock fd d (some ex) e -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Flock" (Val (PairV (#fd) (#how)))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Ht HΦ
  by_cases hW : FsNoErrIno
  · obtain ⟨Sio, hi, -, h2, -⟩ := hW
    haveI := h2
    iapply wp_osFlockP fd how d (some ex) false hE hhow (fun _ => hfree) _ (flockW_noErr hi fd how ex hhow) Φ
      $$ Hinv Hfd Ht
    iintro %e %he Ho
    iapply HΦ $$ [] Ho
    ipureintro
    intro hne
    rcases he with he | he
    · injection he with he; exact absurd (go.intoVal_inj he) hne
    · cases he
  · iapply wp_osFlock fd how d (some ex) false hE hhow (fun _ => hfree) Φ $$ Hinv Hfd Ht
    iintro %e Ho
    iapply HΦ $$ [] Ho
    ipureintro
    exact fun _ => hW

end specs

end Fs
end Perennial

end
