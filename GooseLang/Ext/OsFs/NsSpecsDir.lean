/-
WP specs of the namespace's operations over its whole history (`osNsAll`), for a program that
makes and moves directories (`examples/osfs/walfs`'s `dirswap.go`): the per-directory specs
(`NsSpecs2.lean`, `NsSpecs3.lean`) need their directory a directory in every prefix of the
history (`AllDir`), which a directory made since boot is not. Each takes the whole history `V`
(so no directory fd is open: `rdRes_whole`) and states its premises on the namespace now,
`nsReplay V.2 V.1`. Untrusted.
-/
module

public import GooseLang.Ext.OsFs.NsSpecs3
public import GooseLang.Ext.OsFs.NsMove

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

/-- The history with `o` logged. -/
abbrev nsPush (V : NsMap × List NsOp) (o : NsOp) : NsMap × List NsOp := (V.1, V.2 ++ [o])

/-- `d` is a directory of `m`, or a name in one: a path whose names (`child d b`) the namespace
manages, whatever `d` is now. -/
def NsBelowDir (m : NsMap) (d : GoString) : Prop :=
  m !! d = some .dir ∨ ∃ d0 b0, NameOk b0 ∧ d = child d0 b0 ∧ m !! d0 = some .dir

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- `Regime(d/b)`, a name the namespace manages: `1`. -/
theorem wp_osRegimeG (d b : GoString) (hb : NameOk b) (dq : DFrac) (V : NsMap × List NsOp)
    (hd : NsBelowDir (nsReplay V.2 V.1) d) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osNsAll (L := L) dq V -∗
      (osNsAll (L := L) dq V -∗ Φ (#(1 : w64))) -∗
      WP (ExternalOp osFsExt.name "Regime" (Val (#(child d b)))) @ s; E {{ Φ }} := by
  sorry

/-- `lstat`'s "is it a directory" of `d/b`, nothing there now: `0`. -/
theorem wp_osNsLstatDirG (d b : GoString) (hb : NameOk b) (dq : DFrac) (V : NsMap × List NsOp)
    (hd : nsReplay V.2 V.1 !! d = some .dir) (hn : nsReplay V.2 V.1 !! child d b = none)
    (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osNsAll (L := L) dq V -∗
      (∀ e : w64, osNsAll (L := L) dq V -∗ Φ (PairV (#(0 : w64)) (#e))) -∗
      WP (ExternalOp osFsExt.name "NsLstatDir" (Val (#(child d b)))) @ s; E {{ Φ }} := by
  sorry

/-- `unlink(2)` of `d/b`, a name the namespace manages, with the whole history and the in-flight
flag set: a file is removed (on a failure, removed or not); or it fails, unchanged. -/
theorem wp_osUnlinkG (d b : GoString) (hb : NameOk b) (V : NsMap × List NsOp)
    (hd : NsBelowDir (nsReplay V.2 V.1) d) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osNsAll (L := L) (DFrac.own 1) V -∗ osNsBusy (L := L) true -∗
      (∀ (e : w64) (V' : NsMap × List NsOp),
        ⌜(∃ k, nsReplay V.2 V.1 !! child d b = some (.file k)) ∧
            ((e = 0 ∧ V' = nsPush V (.remove (child d b))) ∨
             (e ≠ 0 ∧ (V' = V ∨ V' = nsPush V (.remove (child d b))))) ∨
          (e ≠ 0 ∧ V' = V)⌝ -∗
        osNsAll (L := L) (DFrac.own 1) V' -∗ osNsBusy (L := L) false -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Unlink" (Val (#(child d b)))) @ s; E {{ Φ }} := by
  sorry

/-- `open(2)` with `O_RDWR | O_CREAT` of `d/b`, nothing there now (`d` a directory now), with the
whole history and the in-flight flag set: the flag cleared; on success a new file under a fresh
key `k` and an fd on it; on failure the file may have been created. -/
theorem wp_osNsOpenCreateG (d b : GoString) (hb : NameOk b) (V : NsMap × List NsOp)
    (hd : nsReplay V.2 V.1 !! d = some .dir) (hn : nsReplay V.2 V.1 !! child d b = none)
    (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osNsAll (L := L) (DFrac.own 1) V -∗ osNsBusy (L := L) true -∗
      (∀ fd : w64, ∀ e : w64, osNsBusy (L := L) false -∗
        ((⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗ ∃ k, ⌜IsInoKey k⌝ ∗
            osNsAll (L := L) (DFrac.own 1) (nsPush V (.create (child d b) k)) ∗
            osMeta (L := L) k (DFrac.own 1) (some newMeta) ∗
            osFd (L := L) fd (DFrac.own 1) ⟨k, true, true⟩) ∨
         (⌜e ≠ 0 ∧ fd = -1⌝ ∗ (osNsAll (L := L) (DFrac.own 1) V ∨ ∃ k, ⌜IsInoKey k⌝ ∗
            osNsAll (L := L) (DFrac.own 1) (nsPush V (.create (child d b) k)) ∗
            osMeta (L := L) k (DFrac.own 1) (some newMeta)))) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp osFsExt.name "NsOpen" (Val (PairV (#(child d b)) (#flCreat)))) @ s; E
        {{ Φ }} := by
  sorry

/-- `open(2)` with `O_RDWR | O_CREAT` of `d/b`, the file of `k` now, with a fraction of `k`'s
`OsMeta` and the in-flight flag set (the retry of a create that made the file): an fd on `k`. -/
theorem wp_osNsOpenCreatExistingG (d b k : GoString) (hb : NameOk b) (dq : DFrac)
    (V : NsMap × List NsOp) (hd : nsReplay V.2 V.1 !! d = some .dir)
    (hf : nsReplay V.2 V.1 !! child d b = some (.file k)) (dqm : DFrac) (mo : Option OsMeta)
    (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osNsAll (L := L) dq V -∗ osMeta (L := L) k dqm mo -∗
      osNsBusy (L := L) true -∗
      (∀ fd : w64, ∀ e : w64, ⌜mo ≠ none⌝ -∗ ⌜(e = 0 ∧ 0 ≤ fd.toInt) ∨ (e ≠ 0 ∧ fd = -1)⌝ -∗
        osNsAll (L := L) dq V -∗ osMeta (L := L) k dqm mo -∗ osNsBusy (L := L) false -∗
        (if e = 0 then osFd (L := L) fd (DFrac.own 1) ⟨k, true, true⟩ else emp) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp osFsExt.name "NsOpen" (Val (PairV (#(child d b)) (#flCreat)))) @ s; E
        {{ Φ }} := by
  sorry

end specs

end Perennial

end
