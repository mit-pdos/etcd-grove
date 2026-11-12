/-
Lean-first (no Rocq counterpart).

# Porcupine: what `checkParallel`'s proof shares (2026-10-14)

`checkParallel` runs one `checkSingle` goroutine per partition `i`; goroutine `i` writes its
cell `longest[i]` and sends its verdict on the buffered channel `results`. The proof's
channel predicate (`resultP`, a bag: Perennial's `isChanBag`) says of a verdict `b`: it comes
from some goroutine `i < n`, with that goroutine's token `i ↪[γt] ()` (a ghost map, so the
verdicts the main thread receives come from distinct goroutines), its cell written
(`cellDone`, persistent: the cell and the `longest` slice it holds, read-only from then on), and
`checkSingle`'s disjunction: `b = true` and partition `i` is linearizable, or `b = false` and
partition `i` is not linearizable or the context was cancelled (`□ PD`, the context's Done
proposition, which only the main thread mints, when it cancels).
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

variable {σ : Type}

/-- `longestLin` made read-only (persistent). -/
def longestLinP (M : SeqModel σ OpV) (l : GoSlice) (h : List (Op OpV)) : IProp GF :=
  iprop(∃ (p : Loc) (sl : GoSlice), l ↦*{DFrac.discard} List.replicate h.length p ∗ p ↦□ sl ∗
    linSlice M h sl)

instance longestLinP_persistent (M : SeqModel σ OpV) (l : GoSlice) (h : List (Op OpV)) :
    Persistent (longestLinP (GF := GF) M l h) := by
  unfold longestLinP; infer_instance

/-- What a goroutine's `longest` says of its partition `h`: it holds a linearization of `h`, or
`h` is not linearizable, or the context is done (`PD`): `checkSingle`'s verdicts, without the
verdict. -/
def linCell (M : SeqModel σ OpV) (l : GoSlice) (h : List (Op OpV)) (PD : IProp GF) : IProp GF :=
  iprop(longestLinP M l h ∨ ⌜¬ Linearizable M h⌝ ∨ □ PD)

instance linCell_persistent (M : SeqModel σ OpV) (l : GoSlice) (h : List (Op OpV)) (PD : IProp GF) :
    Persistent (linCell (GF := GF) M l h PD) := by
  unfold linCell; infer_instance

/-- Goroutine `i` has written its cell `longest[i]` (`lsl` is `longest`), with `linCell` of its
partition (`hs`'s `i`-th). -/
def cellDone (M : SeqModel σ OpV) (hs : List (List (Op OpV))) (PD : IProp GF) (lsl : GoSlice)
    (i : Nat) : IProp GF :=
  iprop(∃ l : GoSlice, typedPointsto (sliceIndexRef GoSlice (i : Int) lsl) l DFrac.discard ∗
    longestPers l ∗ linCell M l (hs.getD i []) PD)

instance cellDone_persistent (M : SeqModel σ OpV) (hs : List (List (Op OpV))) (PD : IProp GF)
    (lsl : GoSlice) (i : Nat) : Persistent (cellDone (GF := GF) M hs PD lsl i) := by
  unfold cellDone; infer_instance

/-- `checkSingle`'s postcondition, read by its goroutine: `longest` read-only, its `linCell`, and
the verdict. -/
theorem checkSingle_post (M : SeqModel σ OpV) (l : GoSlice) (h : List (Op OpV)) (b : Bool)
    (PD : IProp GF) [Persistent PD] :
    ((⌜b = true⌝ ∗ longestLin M l h) ∨
      (⌜b = false⌝ ∗ (⌜¬ Linearizable M h⌝ ∨ □ PD) ∗ longestOwn l h.length)) ⊢
    |==> (longestPers l ∗ linCell M l h PD ∗
      (⌜b = true ∧ Linearizable M h⌝ ∨ (⌜b = false⌝ ∗ (⌜¬ Linearizable M h⌝ ∨ □ PD)))) := by
  iintro (⟨%Hb, Hl⟩ | ⟨%Hb, #Hd, Hlo⟩)
  · iunfold longestLin at Hl
    icases Hl with ⟨%p, %sl, Hl, #Hp, #Hsl⟩
    imod ownSlice_persist l _ _ $$ Hl with #Hl
    ihave #Hsl2 := Hsl
    iunfold linSlice at Hsl2
    icases Hsl2 with ⟨%xs, #Hxs, %Hlin⟩
    imodintro
    isplitr
    · iunfold longestPers
      iexists List.replicate h.length p
      iframe Hl
      iapply (BigSepL.bigSepL_intro (P := iprop(□ (p ↦□ sl ∗ sl ↦*{DFrac.discard} xs) : IProp GF))
        (fun k x hx => by
          rw [List.getElem?_replicate] at hx
          split at hx
          · cases hx
            iintro #⟨Hp', Hxs'⟩
            iright; iexists sl, xs; iframe Hp' Hxs'
          · cases hx))
      imodintro; iframe Hp Hxs
    isplitr
    · iunfold linCell; ileft; iunfold longestLinP; iexists p, sl; iframe Hl Hp Hsl
    · ileft; ipureintro
      exact ⟨Hb, linearizable_of_isLinearization Hlin.2⟩
  · imod longestOwn_persist l h.length $$ Hlo with #Hlp
    imodintro
    iframe Hlp
    isplitr
    · iunfold linCell; iright; iexact Hd
    · iright; iframe Hd; ipureintro; exact Hb

/-- A partition's entry of the info as the computeInfo path builds it: its linearizations, or
the partition is not linearizable, or the context is done. -/
def partD (M : SeqModel σ OpV) (h : List (Op OpV)) (PD : IProp GF) (psl : GoSlice) : IProp GF :=
  iprop(partLins M h psl ∨ ⌜¬ Linearizable M h⌝ ∨ □ PD)

instance partD_persistent (M : SeqModel σ OpV) (h : List (Op OpV)) (PD : IProp GF) (psl : GoSlice) :
    Persistent (partD (GF := GF) M h PD psl) := by
  unfold partD; infer_instance

omit [GooseSemantics] [GooseInterp] in
theorem linearizable_nil (M : SeqModel σ OpV) : Linearizable M ([] : List (Op OpV)) :=
  ⟨[], List.nodup_nil, fun k => by simp, by simp [vals, run], List.Pairwise.nil⟩

/-- Every partition linearizable: each `partD` is its `partLins`, or the context is done. -/
theorem partDs_or (M : SeqModel σ OpV) (PD : IProp GF) [Persistent PD] :
    ∀ (psls : List GoSlice) (f : Nat → List (Op OpV)), (∀ i, Linearizable M (f i)) →
    ([∗list] i ↦ psl ∈ psls, partD M (f i) PD psl) ⊢
      □ PD ∨ [∗list] i ↦ psl ∈ psls, partLins M (f i) psl
  | [], _, _ => by iintro _; iright; iapply BigSepL.bigSepL_nil.2; iempintro
  | a :: l, f, hall => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Ha, H⟩
    icases partDs_or M PD l (fun i => f (i + 1)) (fun i => hall (i + 1)) $$ H with (#HP | H)
    · ileft; iexact HP
    iunfold partD at Ha
    icases Ha with (#Ha | %Hn | #HP)
    · iright; iapply BigSepL.bigSepL_cons.2; iframe H; iexact Ha
    · exact absurd (hall 0) Hn
    · ileft; iexact HP

/-- Cancelling: the token (if still held) mints the Done proposition (`tok_or_pd_persist`, with
a fact beside the Done proposition). -/
theorem tok_or_pd_persist' (γ : GName) (φ : Prop) :
    (dghostVar (GF := GF) γ (DFrac.own 1) () ∨ (□ dghostVar γ DFrac.discard () ∗ ⌜φ⌝)) ⊢
      |==> □ dghostVar γ DFrac.discard () := by
  iintro (Htok | ⟨#Hpd, -⟩)
  · imod dghostVar_persist γ 1 () $$ Htok with #Hpd
    imodintro; iexact Hpd
  · imodintro; iexact Hpd

/-- A `[∗list]` of disjunctions with a common persistent left side. -/
theorem bigSepL_or_left {A : Type} (P : IProp GF) [Persistent P] (Φ : A → IProp GF) (l : List A) :
    ([∗list] x ∈ l, (P ∨ Φ x)) ⊢ P ∨ [∗list] x ∈ l, Φ x := by
  induction l with
  | nil => iintro _; iright; iapply BigSepL.bigSepL_nil.2; iempintro
  | cons a l ih =>
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Ha, H⟩
    icases ih $$ H with (#HP | H)
    · ileft; iexact HP
    icases Ha with (#HP | Ha)
    · ileft; iexact HP
    iright; iapply BigSepL.bigSepL_cons.2; iframe

/-- What a verdict `b` sent on `results` carries (see the file header). -/
def resultP (S : ModelSpec GF σ) (hs : List (List (Theory.Op OpV))) (γt : GName)
    (lsl : GoSlice) (PD : IProp GF) (b : Bool) : IProp GF :=
  iprop(∃ i : Nat, ⌜i < hs.length⌝ ∗ ghostMapElem γt i (DFrac.own 1) () ∗ cellDone S.M hs PD lsl i ∗
    (⌜b = true ∧ ∃ h, hs[i]? = some h ∧ Linearizable S.M h⌝ ∨
      (⌜b = false⌝ ∗ (⌜∃ h, hs[i]? = some h ∧ ¬ Linearizable S.M h⌝ ∨ □ PD))))

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
