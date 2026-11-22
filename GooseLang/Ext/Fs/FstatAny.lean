/-
`fstat(2)` of an fd without the file's `OsMeta` (wal-safe, 2026-11-22, step 2 (D), design (FNE) of
`notes/wal-units/tester.md`): some size, or an errno; errno 0 when the file system does not fail on
any file (`FsNoErrIno`, which `FsNoErrAt` gives). For `os.Stat` of a name whose file the caller does
not hold (a leftover `nm.tmp` that is a file): `fileutil.Exist` then answers `true`. Untrusted.
-/
module

public import GooseLang.Ext.Fs.Specs
public import GooseLang.Ext.Fs.NoErrSpecsOpen

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **`fstat(fd)` of an open fd** (no `OsMeta`): some size with errno 0, or an errno. -/
theorem wp_osFstatAny (fd : w64) (dq : DFrac) (d : OsFd) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗
      (∀ sz : w64, ∀ e : w64, osFd (L := L) fd dq d -∗ Φ (PairV (#sz) (#e))) -∗
      WP (ExternalOp fsExt.name "Fstat" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd HΦ
  iapply wp_os_step "Fstat" _ Φ (by simp) hE (by simp [DataOp]) $$ Hinv
  iintro %st %Γb %Γm %Γf %Γt %h Hw
  unfold osWorld
  icases Hw with ⟨%Hwc, HAb, HAm, HAf, HAt, Htok, Hcells, Hσ⟩
  obtain ⟨hwf, hcoh⟩ := Hwc
  unfold osFd
  icases gFdElem_lookup _ _ _ _ _ _ $$ HAf Hfd with %Hfdl
  icases cellsRes_lookup h _ $$ Hσ Hcells with %Hag
  have hfd : st.proc.fds !! fd = some d := hcoh.fds ▸ Hfdl
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, h, st, ⟨fd, d, st.size d.ino, rfl, hfd, Or.inl rfl, rfl, Or.inl rfl⟩,
      mapsFresh_same rfl, heapRendered_same hwf rfl rfl Hag⟩
  inext
  iintro %e' %h' %st' %Hst
  obtain ⟨Hst, Hfr, Hr⟩ := Hst
  simp only [IsFsStep] at Hst
  obtain ⟨fd', d', sz, hv, hfd', hss, rfl, hres⟩ := Hst
  imod cells_same hwf hwf Hr Hfr rfl rfl $$ [Hσ Hcells] with ⟨Hσ, Hcells⟩
  · iframe
  imodintro
  iexists Γb, Γm, Γf, Γt
  iframe
  isplitr
  · ipureintro; exact ⟨hwf, hcoh⟩
  rcases hres with rfl | ⟨e, he, rfl⟩
  · iapply wp_value'
    iapply HΦ $$ %_ %_ Hfd
  · iapply wp_value'
    iapply HΦ $$ %_ %_ Hfd

/-- **`fstat(fd)` of an open fd** (no `OsMeta`), its errno witnessed: 0 when the file system does not
fail on any file. -/
theorem wp_osFstatAnyW [go.BasicIntoValInj] (fd : w64) (dq : DFrac) (d : OsFd) (hE : ↑osN ⊆ E)
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗
      (∀ sz : w64, ∀ e : w64, ⌜FsNoErrIno → e = 0⌝ -∗ osFd (L := L) fd dq d -∗
        Φ (PairV (#sz) (#e))) -∗
      WP (ExternalOp fsExt.name "Fstat" (Val (#fd))) @ s; E {{ Φ }} := by
  iintro #Hinv Hfd HΦ
  by_cases hne : FsNoErrIno
  · obtain ⟨Sio, hi, h1, -, -⟩ := hne
    haveI := h1
    iapply wp_ext_post "Fstat" (#fd) (by simp) (fun r => ∃ r0, r = PairV r0 (#(0 : w64)))
      (fstat_noErr hi fd) Φ
    iapply wp_osFstatAny fd dq d hE _ $$ Hinv Hfd
    iintro %sz %e Hfd %he
    obtain ⟨r0, he⟩ := he
    obtain ⟨-, h2⟩ := val.PairV.inj he
    have he0 : e = 0 := go.intoVal_inj h2
    iapply HΦ $$ %sz %e [] Hfd
    ipureintro; exact fun _ => he0
  · iapply wp_osFstatAny fd dq d hE _ $$ Hinv Hfd
    iintro %sz %e Hfd
    iapply HΦ $$ %sz %e [] Hfd
    ipureintro; exact fun h => absurd h hne

end specs

end Fs
end Perennial

end
