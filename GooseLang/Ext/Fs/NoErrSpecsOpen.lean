/-
The error-free specs of the extension's calls bbolt's `Open` makes on its file, beyond those of
`NoIoErrSpecs.lean` (`fsync`, a `pwrite`'s end) and `NoMapLockErrSpecs.lean` (`mmap`, `munmap`,
`flock`, `close`): under **no I/O error on chosen files** (`NoIoErr Sio`, every inode covered),
`fstat` returns the size (`wp_osFstatNE`), `pread` a prefix of what it reads, nonempty unless
nothing is there (`wp_osPReadNE`), and the byte-less `fsync` 0 (`wp_osFsyncBNE`), each derived from
its error-able spec by `wp_ext_post`. Untrusted.
-/
module

public import GooseLang.Ext.Fs.NoMapLockErrSpecs

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section step
variable [GooseExts] [GoGlobalContext] [go.BasicIntoValInj] [S : ExtSemantics fsExt] [FsSemOk]

/-- Every step of `fstat(fd)` returns errno 0 when every inode is covered. -/
theorem fstat_noErr {Sio : IoSet} [FsStepSat (NoIoErr Sio)] (hS : ∀ st i, Sio.ino st i) (fd : w64) :
    ∀ h st g e' h' st' g', S.step "Fstat" (#fd) h st g e' h' st' g' →
      ∃ r, e' = Val r ∧ ∃ r0, r = PairV r0 (#(0 : w64)) := by
  intro h st g e' h' st' g' hs
  have hf := fsStepV_of_ne (by decide) (FsSemOk.step_sub _ _ _ _ _ _ _ _ _ hs)
  obtain ⟨hst, -, -⟩ := hf
  simp only [IsFsStep] at hst
  obtain ⟨fd', d, sz, hv, hfd, hsee, -, -⟩ := hst
  have hz := noIoErr_step (Sio := Sio) hs (by simp only [IoCovers]; exact ⟨fd', d, hv, hfd, hS _ _⟩)
    ⟨osRes (#(W64 sz)) 0, st, by
      simp only [IsFsStep]; exact ⟨fd', d, sz, hv, hfd, hsee, by trivial, .inl rfl⟩, ⟨_, rfl⟩⟩
  obtain ⟨r, hr⟩ := (hz : ∃ r : val, e' = osRes r 0)
  exact ⟨_, hr, r, rfl⟩

/-- Every step of `pread(fd, n, off)` returns errno 0 when every inode is covered. -/
theorem pread_noErr {Sio : IoSet} [FsStepSat (NoIoErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (fd off n : w64) :
    ∀ h st g e' h' st' g', S.step "PRead" (PairV (#fd) (PairV (#off) (#n))) h st g e' h' st' g' →
      ∃ r, e' = Val r ∧ ∃ r0, r = PairV r0 (#(0 : w64)) := by
  intro h st g e' h' st' g' hs
  have hf := fsStepV_of_ne (by decide) (FsSemOk.step_sub _ _ _ _ _ _ _ _ _ hs)
  obtain ⟨hst, -, -⟩ := hf
  simp only [IsFsStep] at hst
  obtain ⟨fd', off', n', d, r, hv, hfd, hrd, hoff, hsee, -, -⟩ := hst
  have hk0 : 0 < r.length ∨ r = [] := by rcases r with _ | ⟨a, r⟩ <;> simp
  have hz := noIoErr_step (Sio := Sio) hs
    (by simp only [IoCovers]; exact ⟨fd', d, PairV (#off') (#n'), hv, hfd, hS _ _⟩)
    ⟨osRes (#(r.take r.length)) 0, st, by
      simp only [IsFsStep]
      exact ⟨fd', off', n', d, r, hv, hfd, hrd, hoff, hsee, by trivial,
        .inl ⟨r.length, Nat.le_refl _, hk0, rfl⟩⟩, ⟨_, rfl⟩⟩
  obtain ⟨r, hr⟩ := (hz : ∃ r : val, e' = osRes r 0)
  exact ⟨_, hr, r, rfl⟩

end step

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **`fstat(fd)` with no error** (`wp_osFstat` under `NoIoErr`, every inode covered): the size. -/
theorem wp_osFstatNE {Sio : IoSet} [FsStepSat (NoIoErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (fd : w64) (dq dqm : DFrac) (d : OsFd) (m : OsMeta) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino dqm (m) -∗
      (osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino dqm (m) -∗
        Φ (PairV (#(W64 m.size)) (#(0 : w64)))) -∗
      WP (ExternalOp fsExt.name "Fstat" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Hm HΦ
  iapply wp_ext_post "Fstat" (#fd) (by simp) (fun r => ∃ r0, r = PairV r0 (#(0 : w64)))
    (fstat_noErr hS fd) Φ
  iapply wp_osFstat fd dq dqm d m hE _ $$ Hinv Hfd Hm
  iintro %sz %e %hr Hfd Hm %he
  obtain ⟨r0, he⟩ := he
  obtain ⟨-, h2⟩ := val.PairV.inj he
  have he0 : e = 0 := go.intoVal_inj h2
  subst he0
  rcases hr with ⟨-, rfl⟩ | ⟨h0, -⟩
  · iapply HΦ $$ Hfd Hm
  · exact absurd rfl h0

/-- **`pread(fd, n, off)` with no error** (`wp_osPRead` under `NoIoErr`, every inode covered): a
prefix of the bytes there, nonempty unless none is. -/
theorem wp_osPReadNE {Sio : IoSet} [FsStepSat (NoIoErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (fd off n : w64) (dq dqm dqb : DFrac) (d : OsFd) (m : OsMeta)
    (xs : List (ByteG)) (hE : ↑osN ⊆ E) (hrd : d.readable = true) (hoff : 0 ≤ off.toInt)
    (hlen : xs.length = min n.toNat (m.size - off.toNat)) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino dqm (m) -∗
      osBytes (L := L) d.ino off.toNat dqb xs -∗
      (∀ r : List w8,
        ⌜∃ k ≤ xs.length, r = (xs.map Prod.fst).take k ∧ (0 < k ∨ xs = [])⌝ -∗
        osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino dqm (m) -∗
        osBytes (L := L) d.ino off.toNat dqb xs -∗ Φ (PairV (#r) (#(0 : w64)))) -∗
      WP (ExternalOp fsExt.name "PRead" (Val (PairV (#fd) (PairV (#off) (#n))))) @ s; E
        {{ Φ }} := by
  iintro #Hinv Hfd Hm Hbs HΦ
  iapply wp_ext_post "PRead" _ (by simp [val.isPanic]) (fun r => ∃ r0, r = PairV r0 (#(0 : w64)))
    (pread_noErr hS fd off n) Φ
  iapply wp_osPRead fd off n dq dqm dqb d m xs hE hrd hoff hlen _ $$ Hinv Hfd Hm Hbs
  iintro %r %e %hr Hfd Hm Hbs %he
  obtain ⟨r0, he⟩ := he
  obtain ⟨-, h2⟩ := val.PairV.inj he
  have he0 : e = 0 := go.intoVal_inj h2
  subst he0
  obtain ⟨k, hk, hr, hne⟩ := hr
  iapply HΦ $$ %r [] Hfd Hm Hbs
  ipureintro; exact ⟨k, hk, hr, hne rfl⟩

/-- **The byte-less `fsync(fd)` with no error** (`wp_osFsyncB` under `NoIoErr`, every inode
covered): the file synced. -/
theorem wp_osFsyncBNE {Sio : IoSet} [FsStepSat (NoIoErr Sio)] (hS : ∀ st i, Sio.ino st i)
    (fd : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.ino (DFrac.own 1) m -∗
      (∀ c, osMeta (L := L) d.ino (DFrac.own 1) (m.bsynced c) -∗ osFd (L := L) fd dq d -∗
        Φ (#(0 : w64))) -∗
      WP (ExternalOp fsExt.name "Fsync" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd Hm HΦ
  iapply wp_ext_post "Fsync" (#fd) (by simp) (· = #(0 : w64)) (fsync_noErr hS fd) Φ
  iapply wp_osFsyncB fd dq d m hE _ $$ Hinv Hfd Hm
  iintro %e Hr Hfd %he
  have he0 : e = 0 := go.intoVal_inj he
  subst he0
  icases Hr with (⟨-, %c, Hm⟩ | ⟨%h0, -⟩)
  · iapply HΦ $$ %c Hm Hfd
  · exact absurd rfl h0.1

end specs

end Fs
end Perennial

end
