/-
`unicode/utf8`'s tables `first` and `acceptRanges` (`utf8.go`), which `ValidString` reads, as the
functions its proof computes with (`firstTable`, `acceptTable`), and `utf8Init`, their points-to
facts in those terms, from Perennial's package fact (`unicode.utf8.isInit`: `firstVal`,
`acceptRangesVal`). (Until 2026-10-26 the package was names-only, its fact `True`, in
`v3rpc/Base.lean`; until 2026-11-23 translated here, with its fact `utf8Init`; since then Perennial's.)
-/
module

public import Perennial.Proof.unicode.utf8.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

/-- `first[n]` (`utf8.go`): `as` (`0xF0`) for ASCII, `xx` (`0xF1`) for a byte no sequence
starts with, else the index of the second byte's `acceptRanges` entry (high nibble) and the
sequence's length (low nibble): `s1`..`s7`. -/
def utf8.firstEntry (n : Nat) : w8 :=
  if n < 0x80 then 0xF0
  else if n < 0xC2 then 0xF1
  else if n < 0xE0 then 0x02
  else if n = 0xE0 then 0x13
  else if n = 0xED then 0x23
  else if n < 0xF0 then 0x03
  else if n = 0xF0 then 0x34
  else if n < 0xF4 then 0x04
  else if n = 0xF4 then 0x44
  else 0xF1

/-- The table `first` (`[256]uint8`). -/
def utf8.firstTable : List w8 := (List.range 256).map utf8.firstEntry

/-- The table `acceptRanges` (`[16]acceptRange`): five ranges, the rest zero. -/
def utf8.acceptTable [GooseExts] : List unicode.utf8.acceptRange :=
  [⟨0x80, 0xBF⟩, ⟨0xA0, 0xBF⟩, ⟨0x80, 0x9F⟩, ⟨0x90, 0xBF⟩, ⟨0x80, 0x8F⟩] ++
    List.replicate 11 ⟨0, 0⟩

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `first` and `acceptRanges` hold their tables, read-only. -/
abbrev utf8.utf8Init : IProp GF :=
  iprop(globalAddr unicode.utf8.first ↦□ (array.mk 256 utf8.firstTable : GoArray w8 256) ∗
    globalAddr unicode.utf8.acceptRanges ↦□
      (array.mk 16 utf8.acceptTable : GoArray unicode.utf8.acceptRange 16))

theorem utf8.firstVal_eq : unicode.utf8.firstVal = array.mk 256 utf8.firstTable := by
  set_option maxRecDepth 20000 in rfl

theorem utf8.acceptRangesVal_eq :
    unicode.utf8.acceptRangesVal = array.mk 16 utf8.acceptTable := rfl

/-- Perennial's package fact, in the tables' terms. -/
theorem utf8.utf8Init_of_pkgInit [package_sem : unicode.utf8.Assumptions] :
    isPkgInit (PROP := IProp GF) pkg_id.unicode.utf8 ⊢ utf8.utf8Init (GF := GF) := by
  refine (unicode.utf8.isInit_access (GF := GF)).trans ?_
  unfold unicode.utf8.isInit utf8.utf8Init
  rw [utf8.firstVal_eq, utf8.acceptRangesVal_eq]

end init

end EtcdGrove

end Perennial
