/-
The errors `utilerrors.aggregate`'s `Error()` formats (2026-11-20): a tree whose inner nodes are
`aggregate`s (read-only slices of errors) and whose leaves are errors `fmt` formats by their
`Error()` (`errOk`) and that are no `Aggregate` (no `Errors` method: `aggregate.visit`'s type switch
then takes its `default` arm and calls only the leaf's `Error()`). What conditional authorization
keeps of every error it puts in a decision, so that `fmt.Errorf("%w", err)` of it is safe
(`collectReasonsAndErrors`, `validateConditions`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.fmt.ErrorfErrs
public import GeneratedProof.k8s_io.apimachinery.pkg.util.errors

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace utilerrors

open Iris Iris.BI Iris.ProofMode k8s_io.apimachinery.pkg.util.errors

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A leaf error**: not `nil`, `errOk` (no `Format`, `Error() string` returning some string
needing nothing), and no `Errors` method (so no `Aggregate`: `aggregate.visit` calls only its
`Error()`). -/
def errLeafOk : GoInterface → IProp GF
  | .nil => iprop(False)
  | .ok e => iprop(errOk e ∗ ⌜methodSet e.ty !! go!"Errors" = none⌝)

instance errLeafOk_persistent (e : GoInterface) : Persistent (errLeafOk (GF := GF) e) := by
  cases e <;> unfold errLeafOk <;> infer_instance

/-- **An error tree of depth at most `n`**: a leaf, or an `aggregate` (of the slice `sl`, read-only
for good) of trees of depth at most `n - 1`. -/
def errTreeN : Nat → GoInterface → IProp GF
  | 0, e => errLeafOk e
  | n + 1, e => iprop(errLeafOk e ∨ ∃ (sl : GoSlice) (ys : List GoInterface),
      ⌜e = interface.mkOk aggregate.ty #sl⌝ ∗ sl ↦*□ ys ∗ [∗list] y ∈ ys, errTreeN n y)

instance errTreeN_persistent (n : Nat) (e : GoInterface) :
    Persistent (errTreeN (GF := GF) n e) := by
  induction n generalizing e with
  | zero => unfold errTreeN; infer_instance
  | succ n ih =>
    unfold errTreeN
    have : ∀ ys : List GoInterface, Persistent ([∗list] y ∈ ys, errTreeN (GF := GF) n y) :=
      fun ys => by infer_instance
    infer_instance

/-- **An error tree** (of some depth). -/
def errTree (e : GoInterface) : IProp GF := iprop(∃ n : Nat, errTreeN n e)

instance errTree_persistent (e : GoInterface) : Persistent (errTree (GF := GF) e) := by
  unfold errTree; infer_instance

/-- **`nil` or an error tree**: what a decision's error is. -/
def errTreeOrNil : GoInterface → IProp GF
  | .nil => iprop(True)
  | .ok e => errTree (.ok e)

instance errTreeOrNil_persistent (e : GoInterface) : Persistent (errTreeOrNil (GF := GF) e) := by
  cases e <;> unfold errTreeOrNil <;> infer_instance

theorem errTreeN_mono_succ : ∀ (n : Nat) (e : GoInterface),
    errTreeN (GF := GF) n e ⊢ errTreeN (n + 1) e
  | 0, e => by
    simp only [errTreeN]
    iintro H; ileft; iexact H
  | n + 1, e => by
    rw [errTreeN, errTreeN]
    iintro (H | ⟨%sl, %ys, %he, #Hs, #Hys⟩)
    · ileft; iexact H
    · iright
      iexists sl, ys
      isplitr; · ipureintro; exact he
      isplitr; · iexact Hs
      iapply (BigSepL.bigSepL_mono (fun {_ y} _ => errTreeN_mono_succ n y))
      iexact Hys

theorem errTreeN_mono : ∀ (n m : Nat) (e : GoInterface), n ≤ m →
    errTreeN (GF := GF) n e ⊢ errTreeN m e
  | n, m, e, h => by
    induction m with
    | zero => have : n = 0 := by omega
              subst this; exact .rfl
    | succ m ih =>
      rcases Nat.lt_or_ge n (m + 1) with h' | h'
      · exact (ih (by omega)).trans (errTreeN_mono_succ m e)
      · have : n = m + 1 := by omega
        subst this; exact .rfl

/-- A leaf is a tree. -/
theorem errTree_of_leaf (e : GoInterface) : errLeafOk (GF := GF) e ⊢ errTree e := by
  iintro #H
  unfold errTree
  iexists 0
  simp only [errTreeN]
  iexact H

/-- A tree is not `nil`. -/
theorem errTreeN_ne_nil : ∀ (n : Nat) (e : GoInterface),
    errTreeN (GF := GF) n e ⊢ ⌜e ≠ .nil⌝
  | 0, .nil => by simp only [errTreeN, errLeafOk]; iintro H; iexfalso; iexact H
  | 0, .ok _ => by iintro -; ipureintro; simp
  | n + 1, .nil => by
    rw [errTreeN]
    iintro (H | ⟨%sl, %ys, %he, -⟩)
    · simp only [errLeafOk]; iexfalso; iexact H
    · ipureintro; simp [interface.mkOk] at he
  | n + 1, .ok _ => by iintro -; ipureintro; simp

/-- A tree is `nil` or a tree. -/
theorem errTreeOrNil_of_errTree (e : GoInterface) : errTree (GF := GF) e ⊢ errTreeOrNil e := by
  cases e with
  | nil => unfold errTreeOrNil; iintro -; itrivial
  | ok e => unfold errTreeOrNil; iintro H; iexact H

/-- Trees of some common depth: a list of trees all have depth at most some `n`. -/
theorem errTree_list_bound : ∀ (ys : List GoInterface),
    ([∗list] y ∈ ys, errTree (GF := GF) y) ⊢ ∃ n : Nat, [∗list] y ∈ ys, errTreeN n y
  | [] => by iintro -; iexists 0; iapply BigSepL.bigSepL_nil.2; itrivial
  | y :: ys => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hy, Hys⟩
    ihave ⟨%m, Hys⟩ := errTree_list_bound ys $$ Hys
    unfold errTree
    icases Hy with ⟨%n, Hy⟩
    iexists max n m
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hy]
    · iapply errTreeN_mono n (max n m) y (by omega)
      iexact Hy
    · iapply (BigSepL.bigSepL_mono (fun {_ y} _ => errTreeN_mono m (max n m) y (by omega)))
      iexact Hys

/-- An `aggregate` of trees is a tree. -/
theorem errTree_aggregate (sl : GoSlice) (ys : List GoInterface) :
    sl ↦*□ ys ∗ ([∗list] y ∈ ys, errTree (GF := GF) y) ⊢
      errTree (interface.mkOk aggregate.ty #sl) := by
  iintro ⟨#Hs, Hys⟩
  ihave ⟨%n, #Hys⟩ := errTree_list_bound ys $$ Hys
  unfold errTree
  iexists n + 1
  rw [errTreeN]
  iright
  iexists sl, ys
  isplitr; · ipureintro; rfl
  isplitr; · iexact Hs
  iexact Hys

/-- An `errOk` error of a type without `Errors` is a tree (`fmt.ErrorfLeaf.spec`'s post). -/
theorem errTreeOrNil_of_errOk (e : GoInterfaceOk) (h : methodSet e.ty !! go!"Errors" = none) :
    errOk (GF := GF) e ⊢ errTreeOrNil (.ok e) := by
  iintro #He
  unfold errTreeOrNil
  iapply errTree_of_leaf
  simp only [errLeafOk]
  isplitr; · iexact He
  ipureintro; exact h

theorem errTree_of_errOk (e : GoInterfaceOk) (h : methodSet e.ty !! go!"Errors" = none) :
    errOk (GF := GF) e ⊢ errTree (.ok e) := by
  iintro #He
  iapply errTree_of_leaf
  simp only [errLeafOk]
  isplitr; · iexact He
  ipureintro; exact h

theorem errTreeOrNil_nil : ⊢ errTreeOrNil (GF := GF) GoInterface.nil := by
  unfold errTreeOrNil; itrivial

/-- What `NewAggregate`'s spec says of its result, from errors that are each `nil` or a tree: `nil`
or a tree. -/
theorem errTreeOrNil_of_newAggregate (es : List GoInterface) (a : GoInterface) :
    ([∗list] e ∈ es, errTreeOrNil (GF := GF) e) ∗
      (⌜a = interface.nil⌝ ∨ ∃ (sl : GoSlice) (ys : List GoInterface),
        ⌜a = interface.mkOk aggregate.ty #sl ∧ ∀ y ∈ ys, y ≠ interface.nil ∧ y ∈ es⌝ ∗ sl ↦*□ ys) ⊢
      errTreeOrNil a := by
  iintro ⟨#Hes, Ha⟩
  icases Ha with (%ha | ⟨%sl, %ys, ⟨%ha, %hys⟩, #Hys⟩)
  · subst ha; unfold errTreeOrNil; itrivial
  · subst ha
    have key : ∀ (k : Nat) (y : GoInterface), ys[k]? = some y →
        iprop(□ [∗list] e ∈ es, errTreeOrNil (GF := GF) e) ⊢ errTree y := by
      intro k y hy
      obtain ⟨hne, hmem⟩ := hys y (List.mem_of_getElem? hy)
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hmem
      iintro #H
      ihave #Hy := BigSepL.bigSepL_lookup hj $$ H
      cases y with
      | nil => exact absurd rfl hne
      | ok ii => unfold errTreeOrNil; iexact Hy
    iapply errTreeOrNil_of_errTree
    iapply errTree_aggregate
    isplitr; · iexact Hys
    iapply (BigSepL.bigSepL_intro (P := iprop(□ [∗list] e ∈ es, errTreeOrNil (GF := GF) e))
      (fun k y hy => key k y hy))
    imodintro; iexact Hes

/-- `errTreeOrNil_of_newAggregate` from errors that are each a tree. -/
theorem errTreeOrNil_of_newAggregate' (es : List GoInterface) (a : GoInterface) :
    ([∗list] e ∈ es, errTree (GF := GF) e) ∗
      (⌜a = interface.nil⌝ ∨ ∃ (sl : GoSlice) (ys : List GoInterface),
        ⌜a = interface.mkOk aggregate.ty #sl ∧ ∀ y ∈ ys, y ≠ interface.nil ∧ y ∈ es⌝ ∗ sl ↦*□ ys) ⊢
      errTreeOrNil a := by
  iintro ⟨#Hes, Ha⟩
  iapply errTreeOrNil_of_newAggregate es a
  isplitr
  · iapply (BigSepL.bigSepL_mono (fun {_ y} _ => errTreeOrNil_of_errTree y))
    iexact Hes
  · iexact Ha

end defs

end utilerrors
end EtcdGrove
end Perennial
