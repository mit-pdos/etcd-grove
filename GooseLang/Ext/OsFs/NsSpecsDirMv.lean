/-
The global specs (`NsSpecsDir.lean`) of `rename(2)` of a directory, and of an absent source.
Untrusted.
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

/-- `rename(2)` of the directory `d/bs` to `d/bt`, nothing there now, with the whole history and the
in-flight flag set: moved, its tree with it (on a failure, moved or not); what the move leaves,
looked up: the tree under its new place, nothing under the old, the rest as it was. -/
theorem wp_osRenameDirG (d bs bt : GoString) (hbs : NameOk bs) (hbt : NameOk bt) (hne : bs ≠ bt)
    (V : NsMap × List NsOp) (hd : nsReplay V.2 V.1 !! d = some .dir)
    (hs : nsReplay V.2 V.1 !! child d bs = some .dir) (ht : nsReplay V.2 V.1 !! child d bt = none)
    (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osNsAll (L := L) (DFrac.own 1) V -∗ osNsBusy (L := L) true -∗
      (∀ (e : w64) (V' : NsMap × List NsOp),
        ⌜((e = 0 ∧ V' = nsPush V (.rename (child d bs) (child d bt))) ∨
          (e ≠ 0 ∧ (V' = V ∨ V' = nsPush V (.rename (child d bs) (child d bt))))) ∧
          (∀ r, (r = [] ∨ ∃ r', r = slashB :: r') →
            (NsOp.rename (child d bs) (child d bt)).apply (nsReplay V.2 V.1) !! (child d bt ++ r) =
              nsReplay V.2 V.1 !! (child d bs ++ r)) ∧
          (∀ y, IsUnder (child d bs) y → ¬ IsUnder (child d bt) y →
            (NsOp.rename (child d bs) (child d bt)).apply (nsReplay V.2 V.1) !! y = none) ∧
          (∀ y, ¬ IsUnder (child d bs) y → ¬ IsUnder (child d bt) y →
            (NsOp.rename (child d bs) (child d bt)).apply (nsReplay V.2 V.1) !! y =
              nsReplay V.2 V.1 !! y)⌝ -∗
        osNsAll (L := L) (DFrac.own 1) V' -∗ osNsBusy (L := L) false -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Rename" (Val (PairV (#(child d bs)) (#(child d bt))))) @ s; E
        {{ Φ }} := by
  sorry

/-- `rename(2)` of `d/bs`, nothing there now, to `d/bt`, with the whole history and the in-flight
flag set: it fails, unchanged (the retry of a rename that moved it). -/
theorem wp_osRenameAbsentG (d bs bt : GoString) (hbs : NameOk bs) (hbt : NameOk bt) (hne : bs ≠ bt)
    (V : NsMap × List NsOp) (hd : nsReplay V.2 V.1 !! d = some .dir)
    (hn : nsReplay V.2 V.1 !! child d bs = none) (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osNsAll (L := L) (DFrac.own 1) V -∗ osNsBusy (L := L) true -∗
      (∀ e : w64, ⌜e ≠ 0⌝ -∗ osNsAll (L := L) (DFrac.own 1) V -∗ osNsBusy (L := L) false -∗
        Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Rename" (Val (PairV (#(child d bs)) (#(child d bt))))) @ s; E
        {{ Φ }} := by
  sorry

end specs

end Perennial

end
