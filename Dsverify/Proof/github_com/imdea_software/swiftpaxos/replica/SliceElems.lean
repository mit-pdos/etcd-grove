/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/replica/SliceElems.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
A slice's ownership split into its elements, and back (the lemma `ConnectToPeers` needs to give
disjoint elements of `Peers`, `PeerReaders`, `PeerWriters`, `Alive`, `Ewma` to its goroutines):

* `ownSlice_elems_acc`: `s ↦*{dq} vs` is the elements' points-tos `sliceIndexRef V i s ↦ vs[i]`,
  with a wand giving the slice back holding any list of the same length.
* `bigSepL_replicate_range`: a big separating conjunction over `replicate n x` is one over the
  indices `range n`.
* `bigSepL_exists_range`: a big separating conjunction over the indices `range n` of
  existentials gives one witness list of length `n`.
-/
module

public import Perennial.Golang.Theory.Slice

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode BigSepL Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section pure_bigops
variable {PROP : Type _} [BI PROP] [BIAffine PROP]

theorem bigSepL_replicate_range {A : Type _} (Φ : Nat → A → PROP) (x : A) (n : Nat) :
    ([∗list] i ↦ v ∈ List.replicate n x, Φ i v) ⊣⊢ [∗list] i ↦ _j ∈ List.range n, Φ i x := by
  induction n with
  | zero => exact .rfl
  | succ n ih =>
    rw [List.replicate_succ', List.range_succ]
    refine bigSepL_snoc.trans ?_
    refine BiEntails.trans ?_ bigSepL_snoc.symm
    simp only [List.length_replicate, List.length_range]
    exact ⟨sep_mono ih.1 .rfl, sep_mono ih.2 .rfl⟩

/-- Indices as values: `[∗list] i ↦ j ∈ range n` with `j = i`. -/
theorem bigSepL_range_idx (Φ : Nat → PROP) (n : Nat) :
    ([∗list] i ↦ _j ∈ List.range n, Φ i) ⊣⊢ [∗list] j ∈ List.range n, Φ j := by
  induction n with
  | zero => exact .rfl
  | succ n ih =>
    rw [List.range_succ]
    refine bigSepL_snoc.trans ?_
    refine BiEntails.trans ?_ bigSepL_snoc.symm
    simp only [List.length_range]
    exact ⟨sep_mono ih.1 .rfl, sep_mono ih.2 .rfl⟩

theorem bigSepL_exists_range {X : Type} (Φ : Nat → X → PROP) (n : Nat) :
    ([∗list] j ∈ List.range n, ∃ x, Φ j x) ⊢
      ∃ xs : List X, ⌜xs.length = n⌝ ∗ [∗list] i ↦ x ∈ xs, Φ i x := by
  induction n with
  | zero =>
    iintro _
    iexists []
    isplitr
    · ipureintro; rfl
    · iapply (bigSepL_nil (Φ := Φ)).2; iempintro
  | succ n ih =>
    rw [List.range_succ]
    iintro H
    icases bigSepL_snoc.1 $$ H with ⟨H, %x, Hx⟩
    icases ih $$ H with ⟨%xs, %Hl, Hxs⟩
    iexists xs ++ [x]
    isplitr
    · ipureintro; simp [Hl]
    · iapply bigSepL_snoc.2
      rw [Hl]
      iframe

end pure_bigops

section lemmas

variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [preSem : go.PreSemantics]
variable {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]

/-- A slice is its elements (see the file header). -/
theorem ownSlice_elems_acc (s : GoSlice) (dq : DFrac) (vs : List V) :
    (s ↦*{dq} vs : IProp GF) ⊢
      ([∗list] i ↦ v ∈ vs, typedPointsto (sliceIndexRef V (i : Int) s) v dq) ∗
      (∀ vs' : List V, ⌜vs'.length = vs.length⌝ -∗
        ([∗list] i ↦ v ∈ vs', typedPointsto (sliceIndexRef V (i : Int) s) v dq) -∗
        s ↦*{dq} vs') := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (⟨%Hnil, %Hvs⟩ | ⟨Hsl, %Hl⟩)
  · subst Hvs
    isplitr
    · iapply (bigSepL_nil (Φ := fun (i : Nat) (v : V) =>
        typedPointsto (GF := GF) (sliceIndexRef V (i : Int) s) v dq)).2
      iempintro
    · iintro %vs' %Hl' _
      ileft
      ipureintro
      exact ⟨Hnil, List.eq_nil_of_length_eq_zero Hl'⟩
  · icases typedPointsto_not_null_dup _ _ _ $$ Hsl with ⟨Hsl, %Hnn⟩
    icases typedPointsto_split _ _ _ $$ Hsl with Hsl
    simp only [TypedPointsto.typedPointstoDef]
    icases Hsl with ⟨%Hlen, Hsl⟩
    unfold arrayElems
    have e : ∀ i : Int, arrayIndexRef V i s.ptr = sliceIndexRef V i s := fun _ => rfl
    simp only [e]
    iframe Hsl
    iintro %vs' %Hl' Hsl'
    iright
    isplitl [Hsl']
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      isplitr
      · ipureintro; first | omega | (simp at Hlen ⊢; omega)
      · unfold arrayElems; simp only [e]; iexact Hsl'
    · ipureintro; exact Hl

end lemmas

end Perennial
