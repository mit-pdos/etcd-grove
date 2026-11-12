/-
`Open`'s file after `os.OpenFile` (U11g): the file opened (an existing one holding `D`, or one
just created) as an `OsMeta`, its bytes and the facts of its branch (empty, or an image of a
committed state).
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

/-- **The file `Open` opened** (`O_RDWR | O_CREATE`): its `OsMeta`, its bytes and its branch's
facts (empty, or an image of a committed state). -/
def openedF (i : Ino) (D : Data) : IProp GF :=
  iprop(∃ (m : OsMeta) (xs : List ByteG), osMeta i (DFrac.own 1) m ∗
    osBytes i 0 (DFrac.own 1) xs ∗
    ⌜m.maps = ∅ ∧ xs.length = m.size ∧ m.size < 2 ^ 62 ∧
      ((m.size = 0 ∧ D = ∅) ∨ ∃ C, openOK C D m xs)⌝)

/-- **An existing file holding `D`, opened** (`fileHolds`, its size bound included). -/
theorem fileHolds_opened (i : Ino) (D : Data) :
    fileHoldsDef (GF := GF) i D ⊢ openedF i D := by
  iintro H
  icases fileHolds_decode i D $$ H with ⟨%m, %xs, Hm, Hb, %hml, Hr⟩
  unfold openedF
  iexists m, xs
  iframe Hm Hb
  icases Hr with (%h | ⟨%C, %hC⟩)
  · ipureintro; exact ⟨hml.1, hml.2.1, hml.2.2, Or.inl h⟩
  · ipureintro
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hC
    exact ⟨hml.1, hml.2.1, hml.2.2, Or.inr ⟨C, h1, h2, h3, h4, h5, h6, h7, h8⟩⟩

/-- **A file just created, opened**: empty, holding `∅`. -/
theorem new_opened (i : Ino) :
    osMeta (GF := GF) i (DFrac.own 1) newMeta ⊢ openedF i ∅ := by
  iintro Hm
  unfold openedF
  iexists newMeta, []
  iframe Hm
  isplitr
  · unfold osBytes bytesG; iapply BigSepL.bigSepL_nil.2; iempintro
  ipureintro
  exact ⟨rfl, rfl, by decide, Or.inl ⟨rfl, rfl⟩⟩

end s

end bbolt
end EtcdGrove
end Perennial
