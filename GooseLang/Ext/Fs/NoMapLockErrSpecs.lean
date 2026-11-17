/-
What the program logic may use of the premises **no error of `flock`, `mmap`, `munmap`**
(`NoMapLockErr S`, pending the user's review) and **no I/O error** (`NoIoErr S`) on the calls bbolt's
`Open` and `Close` make on the database file: `munmap` returns 0, a non-blocking `flock` 0 or
`EAGAIN` and `LOCK_UN` 0, `mmap` 0 or `ENOMEM`, a file's `close` 0 (`NoIoErr`), and the error-free specs
of `munmap`, `flock` and `close` derived from their specs by `wp_ext_post`. Every inode covered
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

/-- **A covered lock or mapping call ends `MapLockOk` when it can** (`NoMapLockErr`, from the
semantics' step). -/
theorem noMapLockErr_step {Sio : IoSet} [hsat : FsStepSat (NoMapLockErr Sio)] {o : String}
    {v : val} {h : GMap Loc (NonAtomic val)} {st : OsState} {g : Unit} {e' : Expr}
    {h' : GMap Loc (NonAtomic val)} {st' : OsState} {g' : Unit}
    (hs : S.step o v h st g e' h' st' g') (hc : MapLockCovers Sio o v st)
    (hex : ∃ e'' st'', IsFsStep o v st e'' st'' ∧ MapLockOk o v e'') : MapLockOk o v e' :=
  hsat.sat o v h st g e' h' st' g' hs hc hex

/-- Every step of `munmap` returns 0 when every inode is covered. -/
theorem munmap_noErr {Sio : IoSet} [FsStepSat (NoMapLockErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (v : val) :
    ∀ h st g e' h' st' g', S.step "Munmap" v h st g e' h' st' g' →
      ∃ r, e' = Val r ∧ r = #(0 : w64) := by
  intro h st g e' h' st' g' hs
  have hf := FsSemOk.step_sub _ _ _ _ _ _ _ _ _ hs
  obtain ⟨hst, -, -⟩ := hf
  simp only [IsFsStep] at hst
  obtain ⟨base, len, cap, m, hv, hm, hlen, hcap, -⟩ := hst
  have hz := noMapLockErr_step (Sio := Sio) hs
    (by simp only [MapLockCovers]; exact ⟨base, _, m, hv, hm, hS _ _⟩)
    ⟨Val (#(0 : w64)), st.setProc { st.proc with maps := GMap.delete base st.proc.maps },
      by simp only [IsFsStep]; refine ⟨base, len, cap, m, hv, hm, hlen, hcap, .inl ⟨?_, ?_⟩⟩ <;> trivial,
      (rfl : Val (#(0 : w64)) = Val (#(0 : w64)))⟩
  exact ⟨_, (hz : e' = Val (#(0 : w64))), rfl⟩

/-- Every step of `flock(fd, how)` that unlocks, or is non-blocking, returns 0 or (only a
non-blocking lock request) `EAGAIN`, when every inode is covered. -/
theorem flock_noErr {Sio : IoSet} [FsStepSat (NoMapLockErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (fd how : w64) (req : Option Bool) (nb : Bool) (hhow : flockReq how.toNat = some (req, nb))
    (hk : req = none ∨ nb = true) :
    ∀ h st g e' h' st' g', S.step "Flock" (PairV (#fd) (#how)) h st g e' h' st' g' →
      ∃ r, e' = Val r ∧ (r = #(0 : w64) ∨ (req ≠ none ∧ r = #EAGAIN)) := by
  intro h st g e' h' st' g' hs
  have hf := FsSemOk.step_sub _ _ _ _ _ _ _ _ _ hs
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
        refine ⟨Val (#EAGAIN), st, ?_, Or.inr ⟨fd, how, ex, rfl, ?_, rfl⟩⟩
        · simp only [IsFsStep]
          exact ⟨fd, how, d, some ex, true, rfl, hfd, hhow, hfree,
            .inr ⟨EAGAIN, by decide, fun _ _ => hc, rfl, rfl⟩⟩
        · exact hhow
      · refine ⟨Val (#(0 : w64)), st.setFd fd (d.setLk .flock (some ex)), ?_, Or.inl rfl⟩
        simp only [IsFsStep]
        exact ⟨fd, how, d, some ex, nb, rfl, hfd, hhow, hfree, .inl ⟨hc, rfl, rfl⟩⟩
  have hz := noMapLockErr_step (Sio := Sio) hs
    (by simp only [MapLockCovers]; exact ⟨fd, how, d, rfl, hfd, hS _ _⟩) hex
  rcases (hz : e' = Val (#(0 : w64)) ∨ ∃ (fd1 how1 : w64) (ex : Bool),
      PairV (#fd) (#how) = PairV (#fd1) (#how1) ∧ flockReq how1.toNat = some (some ex, true) ∧
      e' = Val (#EAGAIN)) with hz | ⟨fd1, how1, ex, hv1, hreq, hz⟩
  · exact ⟨_, hz, Or.inl rfl⟩
  · refine ⟨_, hz, Or.inr ⟨?_, rfl⟩⟩
    injection hv1 with h1 h2
    cases go.intoVal_inj h2
    rw [hhow] at hreq
    intro hn; subst hn
    simp at hreq

/-- Every step of `mmap` returns 0 or `ENOMEM` when every inode is covered. -/
theorem mmap_noErr {Sio : IoSet} [FsStepSat (NoMapLockErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (v : val) :
    ∀ h st g e' h' st' g', S.step "Mmap" v h st g e' h' st' g' →
      ∃ r, e' = Val r ∧ ((∃ b, r = PairV b (#(0 : w64))) ∨ r = PairV (#null) (#ENOMEM)) := by
  intro h st g e' h' st' g' hs
  have hf := FsSemOk.step_sub _ _ _ _ _ _ _ _ _ hs
  obtain ⟨hst, -, -⟩ := hf
  simp only [IsFsStep] at hst
  obtain ⟨fd, off, len, prot, fl, d, hv, hfd, hrd, hoff, hlen, hprot, hfl, -⟩ := hst
  have hz := noMapLockErr_step (Sio := Sio) hs
    (by simp only [MapLockCovers]; exact ⟨fd, _, d, hv, hfd, hS _ _⟩)
    ⟨osRes (#null) ENOMEM, st, by
      simp only [IsFsStep]
      exact ⟨fd, off, len, prot, fl, d, hv, hfd, hrd, hoff, hlen, hprot, hfl,
        .inr ⟨ENOMEM, by decide, by trivial, rfl⟩⟩, Or.inr rfl⟩
  rcases (hz : (∃ r : val, e' = osRes r 0) ∨ e' = osRes (#null) ENOMEM) with ⟨r, hr⟩ | hr
  · exact ⟨_, hr, Or.inl ⟨r, rfl⟩⟩
  · exact ⟨_, hr, Or.inr rfl⟩

/-- Every step of a file's `close(fd)` returns 0 when every inode is covered (`NoIoErr`). -/
theorem close_noErr {Sio : IoSet} [FsStepSat (NoIoErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (fd : w64) :
    ∀ h st g e' h' st' g', S.step "Close" (#fd) h st g e' h' st' g' →
      ∃ r, e' = Val r ∧ r = #(0 : w64) := by
  intro h st g e' h' st' g' hs
  have hf := FsSemOk.step_sub _ _ _ _ _ _ _ _ _ hs
  obtain ⟨hst, -, -⟩ := hf
  simp only [IsFsStep] at hst
  obtain ⟨fd', e, d, hv, hfd, -, -⟩ := hst
  have hz := noIoErr_step (Sio := Sio) hs (by simp only [IoCovers]; exact ⟨fd', d, hv, hfd, hS _ _⟩)
    ⟨Val (#(0 : w64)), st.setProc { st.proc with fds := GMap.delete fd' st.proc.fds },
      by simp only [IsFsStep]; exact ⟨fd', 0, d, hv, hfd, rfl, rfl⟩,
      (rfl : Val (#(0 : w64)) = Val (#(0 : w64)))⟩
  exact ⟨_, (hz : e' = Val (#(0 : w64))), rfl⟩

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

end specs

end Fs
end Perennial

end
