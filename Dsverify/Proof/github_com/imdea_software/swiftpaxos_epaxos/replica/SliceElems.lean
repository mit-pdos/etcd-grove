/-
A slice as its element points-tos (package-internal helper): `Peers`, `PeerReaders`,
`PeerWriters`, `Alive` are split by index between the dial loop (indices below `id`) and the
listener goroutine (indices above) while `ConnectToPeers` dials.
-/
module

public import Perennial.Golang.Theory

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [go.Semantics]
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

/-- The element points-tos of the slice `s` holding `vs`. -/
def sliceElems (s : GoSlice) (vs : List V) : IProp GF :=
  iprop([∗list] i ↦ v ∈ vs, typedPointsto (sliceIndexRef V (i : Int) s) v (DFrac.own 1))

/-- A whole slice as its elements, and back with any values of the same length. -/
theorem ownSlice_elems (s : GoSlice) (vs : List V) :
    (s ↦* vs : IProp GF) ⊢ sliceElems s vs ∗
      (∀ vs' : List V, ⌜vs'.length = vs.length⌝ -∗ sliceElems s vs' -∗ s ↦* vs') := by
  rw [ownSlice_unseal]; unfold ownSliceDef sliceElems
  iintro (%H | ⟨Ha, %Hl⟩)
  · obtain ⟨rfl, rfl⟩ := H
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    iintro %vs' %Hlen _
    ileft; ipureintro; exact ⟨rfl, List.eq_nil_of_length_eq_zero Hlen⟩
  · icases typedPointsto_not_null_dup _ _ _ $$ Ha with ⟨Ha, %Hnn⟩
    icases typedPointsto_split _ _ _ $$ Ha with Ha
    simp only [TypedPointsto.typedPointstoDef]
    icases Ha with ⟨%Hlen, Ha⟩
    unfold arrayElems
    simp only [sliceIndexRef]
    iframe Ha
    iintro %vs' %Hlen' Ha
    iright
    isplitl
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      isplitr
      · ipureintro; rw [Hlen']; exact Hlen
      · unfold arrayElems; iexact Ha
    · ipureintro; exact Hl

end

end Perennial
