/-
Lean-first (no Rocq counterpart).

# Porcupine: what `checkParallel`'s proof shares (2026-10-14)

`checkParallel` runs one `checkSingle` goroutine per partition `i`; goroutine `i` writes its
cell `longest[i]` and sends its verdict on the buffered channel `results`. The proof's
channel predicate (`resultP`, a bag: Perennial's `isChanBag`) says of a verdict `b`: it comes
from some goroutine `i < n`, with that goroutine's token `i ↪[γt] ()` (a ghost map, so the
verdicts the main thread receives come from distinct goroutines), its cell written
(`cellDone`, persistent: the cell and the `longest` slice it holds, read-only from then on), and
`checkSingle`'s disjunction: `b = true`, or partition `i` is not linearizable, or the context
was cancelled (`□ PD`, the context's Done proposition, which only the main thread mints, when
it cancels).
-/
module

public import Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.anishathalye.porcupine

open Theory

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- `longestOwn` made read-only (persistent). -/
def longestPers (l : GoSlice) : IProp GF :=
  iprop(∃ ps : List Loc, l ↦*□ ps ∗
    [∗list] p ∈ ps, ⌜p = null⌝ ∨
      ∃ (sl : GoSlice) (xs : List w64), p ↦□ sl ∗ sl ↦*{DFrac.discard} xs)

instance longestPers_persistent (l : GoSlice) : Persistent (longestPers (GF := GF) l) := by
  unfold longestPers; infer_instance

theorem longestOwn_persist (l : GoSlice) (n : Nat) :
    longestOwn (GF := GF) l n ⊢ |==> longestPers l := by
  unfold longestOwn longestPers
  iintro ⟨%ps, Hl, -, #Hps⟩
  imod ownSlice_persist l _ ps $$ Hl with #Hl
  imodintro
  iexists ps
  iframe #

/-- Goroutine `i` has written its cell `longest[i]` (`lsl` is `longest`). -/
def cellDone (lsl : GoSlice) (i : Nat) : IProp GF :=
  iprop(∃ l : GoSlice, typedPointsto (sliceIndexRef GoSlice (i : Int) lsl) l DFrac.discard ∗
    longestPers l)

instance cellDone_persistent (lsl : GoSlice) (i : Nat) :
    Persistent (cellDone (GF := GF) lsl i) := by
  unfold cellDone; infer_instance

variable {σ : Type}

/-- What a verdict `b` sent on `results` carries (see the file header). -/
def resultP (S : ModelSpec GF σ) (hs : List (List (Theory.Op OpV))) (γt : GName)
    (lsl : GoSlice) (PD : IProp GF) (b : Bool) : IProp GF :=
  iprop(∃ i : Nat, ⌜i < hs.length⌝ ∗ ghostMapElem γt i (DFrac.own 1) () ∗ cellDone lsl i ∗
    (⌜b = true⌝ ∨ ⌜∃ h, hs[i]? = some h ∧ ¬ Linearizable S.M h⌝ ∨ □ PD))

theorem bigSepL_replicate_range {A : Type} (Φ : Nat → A → IProp GF) (n : Nat) (v0 : A) :
    ([∗list] i ↦ x ∈ List.replicate n v0, Φ i x) ⊢ [∗list] k ∈ (List.range n : List Nat), Φ k v0 := by
  induction n with
  | zero =>
    simp only [List.replicate_zero, List.range_zero]
    iintro _; iapply BigSepL.bigSepL_nil.2; iempintro
  | succ n ih =>
    rw [List.replicate_succ', List.range_succ]
    iintro H
    icases BigSepL.bigSepL_snoc.1 $$ H with ⟨H, Hl⟩
    iapply BigSepL.bigSepL_snoc.2
    isplitl [H]
    · iapply ih $$ H
    · simp only [List.length_replicate]
      iexact Hl

/-- A slice of copies of one value, as the points-tos of its cells. -/
theorem ownSlice_replicate_cells {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (s : GoSlice) (n : Nat) (v0 : V) :
    (s ↦* (List.replicate n v0) : IProp GF) ⊢
      [∗list] k ∈ (List.range n : List Nat),
        typedPointsto (sliceIndexRef V ((k : Nat) : Int) s) v0 (DFrac.own 1) := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨Hsl, -⟩)
  · have : n = 0 := by simpa using H.2
    subst this
    simp only [List.range_zero]
    iapply BigSepL.bigSepL_nil.2; iempintro
  · icases typedPointsto_split _ _ _ $$ Hsl with Hsl
    simp only [TypedPointsto.typedPointstoDef]
    icases Hsl with ⟨-, Hsl⟩
    unfold arrayElems
    simp only [sliceIndexRef]
    iapply bigSepL_replicate_range $$ Hsl

/-- `n` distinct numbers below `n` are all of them. -/
theorem nodup_all_mem {R : List Nat} {n : Nat} (hnd : R.Nodup) (hlt : ∀ i ∈ R, i < n)
    (hlen : R.length = n) : ∀ i < n, i ∈ R := by
  intro i hi
  refine Classical.byContradiction fun hni => ?_
  have hsub : R ⊆ (List.range n).erase i := by
    intro x hx
    rw [(List.nodup_range).mem_erase_iff]
    exact ⟨fun h => hni (h ▸ hx), List.mem_range.2 (hlt x hx)⟩
  have := hnd.length_le_of_subset hsub
  rw [List.length_erase_of_mem (List.mem_range.2 hi), List.length_range] at this
  omega

/-- A number below `n` not among `R` (distinct, below `n`) leaves room: `R.length < n`. -/
theorem nodup_length_lt {R : List Nat} {n i : Nat} (hnd : R.Nodup) (hlt : ∀ j ∈ R, j < n)
    (hi : i < n) (hni : i ∉ R) : R.length < n := by
  have hsub : R ⊆ (List.range n).erase i := by
    intro x hx
    rw [(List.nodup_range).mem_erase_iff]
    exact ⟨fun h => hni (h ▸ hx), List.mem_range.2 (hlt x hx)⟩
  have := hnd.length_le_of_subset hsub
  rw [List.length_erase_of_mem (List.mem_range.2 hi), List.length_range] at this
  omega

/-- A goroutine's token is not among those already received. -/
theorem toks_fresh (γt : GName) (R : List Nat) (k : Nat) :
    ⊢ ([∗list] i ∈ R, ghostMapElem (GF := GF) γt i (DFrac.own 1) ()) -∗
      ghostMapElem γt k (DFrac.own 1) () -∗ ⌜k ∉ R⌝ := by
  by_cases hin : k ∈ R
  · iintro Htoks Hk
    icases BigSepL.bigSepL_mem_acc hin $$ Htoks with ⟨Hk', -⟩
    icases ghostMapElem_ne γt k k _ () () $$ Hk Hk' with %Hne
    iexfalso; ipureintro; exact Hne rfl
  · iintro _ _; ipureintro; exact hin

/-- The cancel token and the context's Done proposition exclude each other. -/
theorem tok_pd_false (γ : GName) :
    ⊢ dghostVar (GF := GF) γ (DFrac.own 1) () -∗ dghostVar γ DFrac.discard () -∗ False := by
  iintro H1 H2
  icases dghostVar_valid_2 γ () _ () _ $$ H1 H2 with %Hv
  have := DFrac.valid_own_op_discard.1 Hv.1
  have h1 : (1 : Qp).val = 1 := rfl
  rw [h1] at this
  exact absurd this (by decide)

/-- Cancelling: the token (if still held) mints the Done proposition. -/
theorem tok_or_pd_persist (γ : GName) :
    (dghostVar (GF := GF) γ (DFrac.own 1) () ∨ □ dghostVar γ DFrac.discard ()) ⊢
      |==> □ dghostVar γ DFrac.discard () := by
  iintro (Htok | #Hpd)
  · imod dghostVar_persist γ 1 () $$ Htok with #Hpd
    imodintro; iexact Hpd
  · imodintro; iexact Hpd

end defs

end github_com.anishathalye.porcupine

end Perennial
