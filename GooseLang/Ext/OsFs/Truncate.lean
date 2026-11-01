/-
WP specs of the Linux file extension's `ftruncate` (`FtruncateStart`, `FtruncateFinish`), for a
truncate that grows the file (or keeps its size): it takes no byte of the file, and gives it the
new bytes, zeros. The client holds the file's `OsMeta` whole, so no other change is in flight.
While it is in flight, a truncate affects every byte from the size on, so its first step takes
the client's halves of every mapped cell past the size (up to `hi`, where every mapping ends),
and its second step gives them back.
-/
module

public import GooseLang.Ext.OsFs.Write

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open goose_heap

/-- The `OsMeta` of a file while a truncate to `sz` is in flight: the size may become `sz`. -/
def ftMeta (m : OsMeta) (sz : Nat) : OsMeta := { m with hi := max m.hi sz }

/-- The `OsMeta` of a file after a truncate to `sz ≥ m.size`. -/
def OsMeta.grown (m : OsMeta) (sz : Nat) : OsMeta := { m with size := sz, hi := max m.hi sz }

/-- Every mapping of `M` ends at or before `hi`. -/
def MapsBelow (M : GMap Loc Nat) (hi : Nat) : Prop := ∀ b len, M !! b = some len → len ≤ hi

/-- The value of a mapped cell showing the byte `b`. -/
abbrev byteCell [GooseExts] (b : w8) : val := toCellVal (some b)

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- An `ftruncate` to `sz` of the file `p` between its two steps: its first step took the whole
of the file's `OsMeta` `m`. -/
def ftTok (t : Nat) (p : GoString) (sz : Nat) (m : OsMeta) : IProp GF :=
  osTok (L := L) t ⟨⟨p, .truncate sz⟩, 1, [], ftMeta m sz⟩

/-- The file `p`, of `OsMeta` `m`, grown to `sz ≥ m.size`: the whole `OsMeta` (`m.grown sz`), the
new bytes, zeros and dirty, whole, and the client's halves of the cells of every mapping over
`[m.size, sz)`, showing them, and over `[sz, hi)`. -/
def osGrown (p : GoString) (m : OsMeta) (sz hi : Nat) : IProp GF :=
  iprop(osMeta (L := L) p (DFrac.own 1) (some (m.grown sz)) ∗
    osBytes (L := L) p m.size (DFrac.own 1) (List.replicate (sz - m.size) (0, false)) ∗
    mcells m.maps m.size sz (fun _ => byteCell 0) ∗ mcellsAny m.maps sz hi)

/-- The client's halves of the (no) cells of an empty range. -/
theorem mcellsAny_nil (M : GMap Loc Nat) (lo hi : Nat) (h : lo = hi) :
    ⊢ mcellsAny (GF := GF) M lo hi := by
  subst h
  unfold mcellsAny
  refine BigSepM.bigSepM_intro (P := iprop(emp)) (fun _ => ?_)
  iintro -
  iexists (fun _ => #())
  rw [Nat.sub_self]
  unfold cellsR
  simp only [List.range'_zero]
  iapply BigSepL.bigSepL_nil.2
  iempintro

/-- The first step of `ftruncate(fd, sz)` growing the file, with the whole of its `OsMeta`, which
stays with the change until its second step (`wp_FtruncateFinish`), and the client's halves of
the cells of every mapping past the size, which the change affects. -/
theorem wp_FtruncateStart (fd sz : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (hi : Nat)
    (hE : ↑osN ⊆ E) (hwr : d.writable = true) (hsz : 0 ≤ sz.toInt) (hgrow : m.size ≤ sz.toNat)
    (hhi : MapsBelow m.maps hi) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗ osMeta (L := L) d.path (DFrac.own 1) (some m) -∗
      mcellsAny m.maps m.size hi -∗
      (∀ t : Nat, osFd (L := L) fd dq d -∗ ftTok (L := L) t d.path sz.toNat m -∗ Φ (osTokV t)) -∗
      WP (ExternalOp osFsExt.name "FtruncateStart" (Val (PairV (#fd) (#sz)))) @ s; E {{ Φ }} := by
  sorry

/-- The second step of a growing `ftruncate`, giving back the client's halves of the cells of
every mapping past the old size. On success the file is grown (`osGrown`); on failure it may be
grown, or unchanged. -/
theorem wp_FtruncateFinish (t : Nat) (p : GoString) (sz : Nat) (m : OsMeta) (hi : Nat)
    (hE : ↑osN ⊆ E) (hgrow : m.size ≤ sz) (hhi : MapsBelow m.maps hi) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ ftTok (L := L) t p sz m -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ osGrown (L := L) p m sz hi) ∨
         (⌜e ≠ 0⌝ ∗ (osGrown (L := L) p m sz hi ∨
           (osMeta (L := L) p (DFrac.own 1) (some m) ∗ mcellsAny m.maps m.size hi)))) -∗
        Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "FtruncateFinish" (Val (osTokV t))) @ s; E {{ Φ }} := by
  sorry

end specs

end Perennial
