/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/N/SliceElems.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

# Unit N: a slice as its elements' points-tos

`ConnectToPeers` and `waitForPeerConnections` write disjoint elements of the generic replica's
`Peers`, `PeerReaders`, `PeerWriters`, `Alive` slices from two goroutines: the slice is split
into its elements (`ownSlice_elems`) and rebuilt from them (`ownSlice_of_elems`).
-/
module

public import Perennial.Golang.Theory.Slice

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode BigSepL

noncomputable section
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

/-- The shape of a non-empty slice's header. -/
def sliceShape (s : GoSlice) (n : Nat) : Prop :=
  sint.Z s.len = n ∧ sint.Z s.len ≤ sint.Z s.cap ∧ s.ptr ≠ null

/-- A non-empty slice is its elements' points-tos. -/
theorem ownSlice_elems (s : GoSlice) (vs : List V) (hne : vs ≠ []) :
    (s ↦* vs : IProp GF) ⊢ ⌜sliceShape s vs.length⌝ ∗
      [∗list] i ↦ v ∈ vs, typedPointsto (sliceIndexRef V (i : Int) s) v (DFrac.own 1) := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨Hsl, %Hl⟩)
  · exact absurd H.2 hne
  icases typedPointsto_not_null_dup _ _ _ $$ Hsl with ⟨Hsl, %Hnn⟩
  icases typedPointsto_split _ _ _ $$ Hsl with Hsl
  simp only [TypedPointsto.typedPointstoDef]
  icases Hsl with ⟨%Hlen, Hel⟩
  isplitr
  · ipureintro; exact ⟨by revert Hlen; omega, Hl, Hnn⟩
  simp only [arrayElems, sliceIndexRef]
  iexact Hel

/-- A slice from its elements' points-tos. -/
theorem ownSlice_of_elems (s : GoSlice) (vs : List V) (h : sliceShape s vs.length) :
    ([∗list] i ↦ v ∈ vs, typedPointsto (GF := GF) (sliceIndexRef V (i : Int) s) v (DFrac.own 1))
      ⊢ s ↦* vs := by
  obtain ⟨hl, hc, hnn⟩ := h
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro Hel
  iright
  isplitl
  · iapply typedPointsto_combine _ _ _ hnn
    simp only [TypedPointsto.typedPointstoDef]
    isplitr
    · ipureintro; omega
    simp only [arrayElems, sliceIndexRef] at *
    iexact Hel
  · ipureintro; exact hc

end

end Perennial.gryff
