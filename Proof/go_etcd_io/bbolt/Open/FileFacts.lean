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
facts (empty, or an image of a committed state), and the size bound `B` the opener knows (session
S3f: `fileHoldsM`'s mappable size for `Open_sharedNoErr`, nothing otherwise). -/
def openedF (i : Ino) (D : Data) (B : Nat → Prop) : IProp GF :=
  iprop(∃ (m : OsMeta) (xs : List ByteG), osMeta i (DFrac.own 1) m ∗
    osBytes i 0 (DFrac.own 1) xs ∗
    ⌜m.maps = ∅ ∧ xs.length = m.size ∧ (m.size < 2 ^ 62 ∧ m.size % 4096 = 0) ∧
      ((m.size = 0 ∧ D = ∅) ∨ ∃ C, openOK C D m xs)⌝ ∗ ⌜B m.size⌝ ∗ fileRcpt (xs.map Prod.fst))

/-- `openedF` of equal arguments (made here so that `simp`'s congruence lemma for `openedF`, which
`Open`'s proof needs, is this module's, not a spec's proof file's: `etc/api/bbolt-layout.txt`). -/
theorem openedF_congr {i i' : Ino} {D D' : Data} {B : Nat → Prop} (hi : i = i') (hD : D = D') :
    openedF (GF := GF) i D B = openedF i' D' B := by
  simp only [hi, hD]

/-- **An existing file holding `D`, opened** (`fileHolds`, its size bound included). -/
theorem fileHolds_opened (i : Ino) (D : Data) :
    fileHoldsDef (GF := GF) i D ⊢ openedF i D (fun _ => True) := by
  iintro H
  icases fileHolds_decode i D $$ H with ⟨%m, %xs, Hm, Hb, %hml, #Hrc, Hr⟩
  unfold openedF
  iexists m, xs
  iframe Hm Hb Hrc
  icases Hr with (%h | ⟨%C, %hC⟩)
  · ipureintro; exact ⟨hml.1, hml.2.1, hml.2.2, Or.inl h⟩
  · ipureintro
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hC
    exact ⟨hml.1, hml.2.1, hml.2.2, Or.inr ⟨C, h1, h2, h3, h4, h5, h6, h7, h8⟩⟩

/-- **An existing mappable file holding `D`, opened** (session S3f: `fileHoldsM`). -/
theorem fileHoldsM_opened (i : Ino) (D : Data) :
    fileHoldsMDef (GF := GF) i D ⊢ openedF i D (· ≤ 0xFFFFFFFFFFFF) := by
  unfold fileHoldsMDef openedF
  iintro ⟨%m, %xs, Hm, Hb, %h, %hB, #Hrc⟩
  iexists m, xs
  iframe Hm Hb Hrc
  isplitr
  · ipureintro
    obtain ⟨h1, h2, h3, h4⟩ := h
    rcases h4 with h4 | ⟨C, c1, c2, c3, c4, c5, c6, c7, c8⟩
    · exact ⟨h1, h2, h3, Or.inl h4⟩
    · exact ⟨h1, h2, h3, Or.inr ⟨C, c1, c2, c3, c4, c5, c6, c7, c8⟩⟩
  · ipureintro; exact hB

/-- **A file just created, opened**: empty, holding `∅`. -/
theorem new_opened (i : Ino) (B : Nat → Prop) (hB : B 0) :
    osMeta (GF := GF) i (DFrac.own 1) newMeta ⊢ openedF i ∅ B := by
  iintro Hm
  unfold openedF
  iexists newMeta, []
  iframe Hm
  isplitr
  · unfold osBytes bytesG; iapply BigSepL.bigSepL_nil.2; iempintro
  isplitr
  · ipureintro
    exact ⟨rfl, rfl, by decide, Or.inl ⟨rfl, rfl⟩⟩
  isplitr
  · ipureintro; exact hB
  unfold fileRcpt
  ileft; ipureintro
  exact fun C h => fileImage_nil_not C (by simpa using h)

end s

end bbolt
end EtcdGrove
end Perennial
