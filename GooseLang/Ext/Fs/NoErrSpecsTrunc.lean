/-
`open(2)` in the shared mode with its error witnessed (wal-fsfix2): `O_CREAT` (`wp_osOpenCreateSW`) and
`O_TRUNC` of an existing file (`wp_osOpenTruncSW`), each a failure's errno `EINTR` (which every model
of `open` retries) unless the file system can fail on the path or the path does not fit (the witness
`¬ (FsNoErrOn (· = p) ∧ PathFits p)`), from `NoIoErr`/`NoMapLockErr` (`open_failure_eintr`) over the
generic specs (`wp_osOpenCreateSQ`, `wp_osOpenTruncSQ`). Untrusted.
-/
module

public import GooseLang.Ext.Fs.NoErrSpecsOpenFile
public import GooseLang.Ext.Fs.TreeSharedTrunc

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [S : ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- **`open(O_CREAT)` of `d/b`, its error witnessed** (`wp_osOpenCreateS'`, the name absent or no
`O_TRUNC`): a failure's errno `EINTR`, or the witness. -/
theorem wp_osOpenCreateSW (R : Roots) (d b : GoString) (j : Ino) (dq : DFrac) (h : NamesH)
    (k s0 : Nat) (q : Qp) (fl : w64) (hfl : OpenFlagsOk fl.toNat) (hcr : fl.toNat / O_CREAT % 2 = 1)
    (htr : fl.toNat / O_TRUNC % 2 = 0 ∨ h.cur !! b = none) (hb : NameOk b) (hnd : ∀ J, h.cur !! b ≠ some (.dir J))
    (hs : h.next ≤ s0) (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j (.only [b]) (DFrac.own 1) h -∗ osCallS (L := L) k s0 (child d b) q -∗
      (∀ fd : w64, ∀ e : w64,
        ⌜e ≠ 0 → e = EINTR ∨ ¬ (FsNoErrOn (· = child d b) ∧ PathFits (child d b))⌝ -∗
        osCallPerm (L := L) (callKey R d) q -∗ osPathS (L := L) R d dq j -∗
        ((∃ i, ⌜h.cur !! b = some (.file i)⌝ ∗ osNames (L := L) j (.only [b]) (DFrac.own 1) h ∗
            (⌜e ≠ 0 ∧ fd = -1⌝ ∨ ⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗ osFd (L := L) fd (DFrac.own 1) (openFd i fl))) ∨
         (⌜h.cur !! b = none⌝ ∗ ∃ x i, osLogged (L := L) x (⟨.create j b i, s0⟩ : LogEntry) ∗
            osNames (L := L) j (.only [b]) (DFrac.own 1) (h.log x (⟨.create j b i, s0⟩ : LogEntry) (<[b := .file i]> h.cur)) ∗
            osMeta (L := L) i (DFrac.own 1) newMeta ∗
            (⌜e ≠ 0 ∧ fd = -1⌝ ∨ ⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗ osFd (L := L) fd (DFrac.own 1) (openFd i fl))) ∨
         (⌜e ≠ 0 ∧ fd = -1⌝ ∗ osNames (L := L) j (.only [b]) (DFrac.own 1) h)) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#(child d b)) (#fl)))))
        @ s; E {{ Φ }} :=
  wp_osOpenCreateSQ R d b j dq h k s0 q fl hfl hcr htr hb hnd hs hE hE' Φ
    (fun e => e = EINTR ∨ ¬ (FsNoErrOn (· = child d b) ∧ PathFits (child d b)))
    (fun st _e' _st' hw hcall hp hent Hst Hsem fd e he hne => by
      by_cases hW : FsNoErrOn (· = child d b) ∧ PathFits (child d b)
      · obtain ⟨⟨Sio, -, h1, h2, hpp⟩, hf⟩ := hW
        haveI := h1; haveI := h2
        obtain ⟨hh, hh', Hsem⟩ := Hsem
        exact .inl (open_failure_eintr ⟨hpp _ rfl, hf⟩
          (openCreate_succ hfl hcr (htr.imp id (fun h0 => by rw [hent]; exact h0)) hw hcall hp hb
            (fun J => by rw [hent]; exact hnd J)) Hst Hsem fd e he hne)
      · exact .inr hW)

/-- **`open(O_TRUNC)` of `d/b`, a name holding the file `i`, its error witnessed**
(`wp_osOpenTruncS`): a failure's errno `EINTR`, or the witness. -/
theorem wp_osOpenTruncSW (R : Roots) (d b : GoString) (j i : Ino) (N : NameSet) (dq dqn : DFrac)
    (h : NamesH) (k s0 : Nat) (q : Qp) (fl : w64) (m : OsMeta) (xs : List ByteG)
    (hfl : OpenFlagsOk fl.toNat) (htr : fl.toNat / O_TRUNC % 2 = 1) (hb : NameOk b)
    (hN : N.Mem b) (hi : h.cur !! b = some (.file i)) (hlen : xs.length = m.size)
    (hE : ↑osN ⊆ E) (hE' : ↑osShN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osSharedInv (L := L) R -∗ osPathS (L := L) R d dq j -∗
      osNames (L := L) j N dqn h -∗ osCallS (L := L) k s0 (child d b) q -∗
      osMeta (L := L) i (DFrac.own 1) m -∗ osBytes (L := L) i 0 (DFrac.own 1) xs -∗
      mcellsAny (GF := GF) m.maps 0 (pageEnd m.size) -∗
      (∀ fd : w64, ∀ e : w64, ⌜(e = 0 ∧ 0 ≤ fd.toInt) ∨ (e ≠ 0 ∧ fd = -1 ∧
          (e = EINTR ∨ ¬ (FsNoErrOn (· = child d b) ∧ PathFits (child d b))))⌝ -∗
        osCallPerm (L := L) (callKey R d) q -∗ osPathS (L := L) R d dq j -∗ osNames (L := L) j N dqn h -∗
        ((⌜e ≠ 0⌝ ∗ osMeta (L := L) i (DFrac.own 1) m ∗ osBytes (L := L) i 0 (DFrac.own 1) xs ∗
            mcellsAny (GF := GF) m.maps 0 (pageEnd m.size)) ∨
         (∃ n, rsDone (L := L) true i 0 0 m n)) -∗
        (if e = 0 then osFd (L := L) fd (DFrac.own 1) (openFd i fl) else emp) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#(child d b)) (#fl)))))
        @ s; E {{ Φ }} :=
  wp_osOpenTruncSQ R d b j i N dq dqn h k s0 q fl m xs hfl htr hb hN hi hlen hE hE' Φ
    (fun e => e = EINTR ∨ ¬ (FsNoErrOn (· = child d b) ∧ PathFits (child d b)))
    (fun st e' st' hw hcall hl Hst Hsem fd e he hne => by
      by_cases hW : FsNoErrOn (· = child d b) ∧ PathFits (child d b)
      · obtain ⟨⟨Sio, -, h1, h2, hpp⟩, hf⟩ := hW
        haveI := h1; haveI := h2
        obtain ⟨hh, hh', Hsem⟩ := Hsem
        have Hst' := Hst
        simp only [IsFsStep] at Hst'
        replace Hst' := open_inTree Hst' (treePath_of_lookup hl)
        obtain ⟨p', fl', k', s', hv, -, -, hk', hres⟩ := Hst'
        obtain ⟨rfl, rfl, rfl⟩ := tokPathFl_inj hv
        have hnb : ¬ BusyAt (st.metaEnd k) i := hres.1 (by simp [htr]) i hl
        exact .inl (open_failure_eintr ⟨hpp _ rfl, hf⟩ (openTrunc_succ hfl htr hw hcall hl hnb) Hst Hsem
          fd e he hne)
      · exact .inr hW)

end specs

end Fs
end Perennial

end
