/-
The global specs (`NsSpecsDir.lean`) of `mkdir(2)` and `rmdir(2)`. Untrusted.
-/
module

public import GooseLang.Ext.OsFs.NsSpecsDir

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- `rmdir(2)` of `d/b`, a name the namespace manages, with the whole history and the in-flight
flag set: an empty directory is removed (on a failure, removed or not); or it fails, unchanged. -/
theorem wp_osRmdirG (d b : GoString) (hb : NameOk b) (V : NsMap × List NsOp)
    (hd : NsBelowDir (nsReplay V.2 V.1) d) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osNsAll (L := L) (DFrac.own 1) V -∗ osNsBusy (L := L) true -∗
      (∀ (e : w64) (V' : NsMap × List NsOp),
        ⌜(nsReplay V.2 V.1 !! child d b = some .dir ∧
            (∀ c, NameOk c → nsReplay V.2 V.1 !! child (child d b) c = none) ∧
            ((e = 0 ∧ V' = nsPush V (.remove (child d b))) ∨
             (e ≠ 0 ∧ (V' = V ∨ V' = nsPush V (.remove (child d b)))))) ∨
          (e ≠ 0 ∧ V' = V)⌝ -∗
        osNsAll (L := L) (DFrac.own 1) V' -∗ osNsBusy (L := L) false -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Rmdir" (Val (#(child d b)))) @ s; E {{ Φ }} := by
  sorry

/-- `mkdir(2)` of `d/b`, a name the namespace manages, with the whole history and the in-flight
flag set: where nothing is, in a directory, a new directory (on a failure, made or not); or it
fails, unchanged. -/
theorem wp_osMkdirG (d b : GoString) (hb : NameOk b) (V : NsMap × List NsOp)
    (hd : NsBelowDir (nsReplay V.2 V.1) d)
    (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osNsAll (L := L) (DFrac.own 1) V -∗ osNsBusy (L := L) true -∗
      (∀ (e : w64) (V' : NsMap × List NsOp),
        ⌜(nsReplay V.2 V.1 !! child d b = none ∧ nsReplay V.2 V.1 !! d = some .dir ∧
            (∀ c, nsReplay V.2 V.1 !! child (child d b) c = none) ∧
            ((e = 0 ∧ V' = nsPush V (.mkdir (child d b))) ∨
             (e ≠ 0 ∧ (V' = V ∨ V' = nsPush V (.mkdir (child d b)))))) ∨
          (e ≠ 0 ∧ V' = V)⌝ -∗
        osNsAll (L := L) (DFrac.own 1) V' -∗ osNsBusy (L := L) false -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Mkdir" (Val (#(child d b)))) @ s; E {{ Φ }} := by
  sorry

end specs

end Perennial

end
