/-
`Open`'s file before and after `os.OpenFile` (U11g): `fileHolds` as an `OsMeta` option and what
`Open` needs of each case (`openRest`), and the file opened (created if absent) as an `OsMeta`,
its bytes and the facts of its branch (empty, or an image of a committed state).
-/
module

public import Proof.go_etcd_io.bbolt.Open.Facts

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode

section s
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- What `Open` holds of the file at `path` besides its `OsMeta` option `mo`. -/
def openRest (path : GoString) (D : Data) : Option OsMeta → IProp GF
  | none => iprop(⌜D = ∅⌝)
  | some m => iprop(∃ xs : List ByteG, osBytes path.ino 0 (DFrac.own 1) xs ∗
      ⌜m.maps = ∅ ∧ xs.length = m.size ∧ m.size < 2 ^ 62 ∧
        ((m.size = 0 ∧ D = ∅) ∨ ∃ C, openOK C D m xs)⌝)

/-- **`fileHolds` as `Open` uses it** (its size bound, maintainer 12's item 5, included). -/
theorem fileHolds_openRest (path : GoString) (D : Data) :
    fileHoldsDef (GF := GF) path D ⊢ ∃ mo : Option OsMeta, osMeta path.ino (DFrac.own 1) mo ∗
      openRest path D mo := by
  iintro H
  icases fileHolds_decode path D $$ H with (⟨Hm, %hD⟩ | ⟨%m, %xs, Hm, Hb, %hml, Hr⟩)
  · iexists none; iframe Hm; unfold openRest; ipureintro; exact hD
  have hsz : m.size < 2 ^ 62 := hml.2.2
  iexists some m; iframe Hm; unfold openRest; iexists xs; iframe Hb
  icases Hr with (%h | ⟨%C, %hC⟩)
  · ipureintro; exact ⟨hml.1, hml.2.1, hsz, Or.inl h⟩
  · ipureintro
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hC
    exact ⟨hml.1, hml.2.1, hsz, Or.inr ⟨C, h1, h2, h3, h4, h5, h6, h7, h8⟩⟩

/-- **The file opened** (`O_RDWR | O_CREATE`): an `OsMeta`, its bytes and its branch's facts. -/
theorem openRest_opened (path : GoString) (D : Data) (mo : Option OsMeta) :
    osMeta (GF := GF) path.ino (DFrac.own 1) (openMeta mo true) ∗ openRest path D mo ⊢
      ∃ (m : OsMeta) (xs : List ByteG), osMeta path.ino (DFrac.own 1) m ∗
        osBytes path.ino 0 (DFrac.own 1) xs ∗
        ⌜m.maps = ∅ ∧ xs.length = m.size ∧ m.size < 2 ^ 62 ∧
          ((m.size = 0 ∧ D = ∅) ∨ ∃ C, openOK C D m xs)⌝ := by
  cases mo with
  | none =>
    unfold openRest
    simp only [openMeta]
    iintro ⟨Hm, %hD⟩
    iexists newMeta, []
    iframe Hm
    isplitr
    · unfold osBytes bytesG; iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro
    exact ⟨rfl, rfl, by decide, Or.inl ⟨rfl, hD⟩⟩
  | some m =>
    unfold openRest
    simp only [openMeta]
    iintro ⟨Hm, %xs, Hb, %h⟩
    iexists m, xs
    iframe Hm Hb
    ipureintro; exact h

end s

end bbolt
end EtcdGrove
end Perennial
