/- Lean-first (no Rocq counterpart).

# Error trees for `errors.Is`: what they give, and how they are built

`Spec/errors/ErrTree.lean`'s `errTreeNot`/`errTreeTerm` give the triples of `errors.Is` the WAL's specs state
(`errIsNot`, `errIsTerm`) through Perennial's `errors.wp_Is_tree`; a leaf `*errors.errorString` has them, and a
`*fmt.wrapError` of an error that has them has them too (its `Unwrap` returns the error, and it has no `Is`).
-/
module

public import Spec.errors.ErrTree
public import Spec.fmt.ErrorfErrsNot
public import Perennial.Proof.errors.Results
public import Perennial.Proof.fmt.Errorf
public import Proof.errors.NewVar

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section tree
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [errs_sem : _root_.Perennial.errors.Assumptions]

/-- `errTreeNot`'s pure part. -/
theorem errTreeNot_ne (e t : GoInterface) : errTreeNot (GF := GF) e t ⊢ ⌜e ≠ t⌝ := by
  unfold errTreeNot
  iintro ⟨%h, -⟩
  ipureintro; exact h

/-- **`errTreeNot` gives `errIsNot`** at a pointer target. -/
theorem errIsNot_of_tree (e t : GoInterface)
    (ht : ∀ tii, t = interface.ok tii → _root_.Perennial.errors.IsPointerError tii) :
    isPkgInit (PROP := IProp GF) pkg_id.errors ⊢ errTreeNot (GF := GF) e t -∗ errIsNot e t := by
  iintro #Hi #Htr
  unfold errTreeNot
  icases Htr with ⟨%hne, %S, %M, #Htree, %hS, %hty, %hno⟩
  unfold errIsNot
  isplitr
  · ipureintro; exact hne
  imodintro
  imodintro
  iintro %Φ - HΦ
  wp_apply +noauto _root_.Perennial.errors.wp_Is_tree S M e t ht hty $$ [$Hi $Htree]
    as %b ⟨%Hnil, -, %Hsome⟩
  · ipureintro; exact hS
  have hb : b = false := by
    cases b
    · rfl
    · exfalso
      cases t with
      | nil =>
        have := Hnil (Or.inr rfl)
        exact hne (of_decide_eq_true this.symm)
      | ok tii =>
        cases e with
        | nil =>
          have := Hnil (Or.inl rfl)
          exact hne (of_decide_eq_true this.symm)
        | ok ei =>
          obtain ⟨ii, hii, hm⟩ := Hsome tii rfl (ht tii rfl) (by simp) rfl
          rcases hm with hm | hm
          · exact (hno ii hii).1 hm
          · exact (hno ii hii).2 hm
  rw [hb]
  iapply HΦ
  itrivial

/-- **`errTreeTerm` gives `errIsTerm`.** -/
theorem errIsTerm_of_tree (e : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.errors ⊢ errTreeTerm (GF := GF) e -∗ errIsTerm e := by
  iintro #Hi #Htr
  unfold errIsTerm
  iintro !> %u %hu
  unfold errTreeTerm
  ihave ⟨%S, %M, #Htree, %hS, %hty⟩ := Htr $$ %u %hu
  iintro !> %Φ - HΦ
  wp_apply +noauto _root_.Perennial.errors.wp_Is_tree S M e u hu hty $$ [$Hi $Htree] as %b -
  · ipureintro; exact hS
  iapply HΦ
  itrivial

/-- **A leaf `*errorString` that is not `t`**, at a pointer target `t`. -/
theorem errTreeNot_errorString [ErrorStringLeaf] (x : Loc) (t : GoInterface)
    (hne : interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x ≠ t) :
    ⊢ errTreeNot (GF := GF) (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x)
      t := by
  obtain ⟨hp, hleaf, hIs⟩ := EtcdGrove.errorString_leaf x
  unfold errTreeNot
  isplitr
  · ipureintro; exact hne
  iexists (· = interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x), (fun _ => False)
  isplitl
  · iapply _root_.Perennial.errors.errorIsTree_leaf _ _ _ hleaf hIs
  ipureintro
  refine ⟨rfl, _root_.Perennial.errors.treeTyped_pointer _ t hp, fun ii hii => ⟨?_, id⟩⟩
  rw [hii]; exact hne

/-- **A leaf `*errorString`** has a tree at every pointer target. -/
theorem errTreeTerm_errorString [ErrorStringLeaf] (x : Loc) :
    ⊢ errTreeTerm (GF := GF)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) := by
  obtain ⟨hp, hleaf, hIs⟩ := EtcdGrove.errorString_leaf x
  unfold errTreeTerm
  iintro !> %u %hu
  iexists (· = interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x), (fun _ => False)
  isplitl
  · iapply _root_.Perennial.errors.errorIsTree_leaf _ _ _ hleaf hIs
  ipureintro
  exact ⟨rfl, _root_.Perennial.errors.treeTyped_pointer _ u hp⟩

end tree

/-! ## A `*fmt.wrapError` -/

section wrap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [errs_sem : _root_.Perennial.errors.Assumptions] [fmt_sem : _root_.Perennial.fmt.Assumptions]

/-- `*fmt.wrapError`'s methods: no `Is`, `Unwrap() error`. -/
theorem wrapError_methods :
    methodSet (go.GoType.PointerType _root_.Perennial.fmt.wrapError.ty) !! go!"Is" = none ∧
    methodSet (go.GoType.PointerType _root_.Perennial.fmt.wrapError.ty) !! go!"Unwrap" =
      some (go.Signature [] false [go.error]) := by
  have h1 := go.MethodSetIs.method_set_is
    (t := go.GoType.PointerType _root_.Perennial.fmt.wrapError.ty) go!"Is"
  have h2 := go.MethodSetIs.method_set_is
    (t := go.GoType.PointerType _root_.Perennial.fmt.wrapError.ty) go!"Unwrap"
  refine ⟨?_, ?_⟩
  · rw [h1]; try decide
  · rw [h2]; try simp [go.methodSetLookup]

/-- `(*fmt.wrapError).Unwrap` returns its `err` field. -/
theorem wp_wrapError_Unwrap (l : Loc) (c : GoInterface) :
    {{ (l.[fmt.wrapError, go!"err"] ↦□ c : IProp GF) }}
      (App (Val #(methods (go.GoType.PointerType _root_.Perennial.fmt.wrapError.ty) go!"Unwrap" #l)) (Val #()))
    {{ RET #c; True }} := by
  wp_start as #Hc
  wp_auto
  iapply HΦ
  itrivial

/-- The tree of a `*fmt.wrapError` `w` of `c`: `w` added to `c`'s tree (`M` restricted to the other errors: `w`
has no `Is`). -/
theorem wrap_errorIsTree (S : GoError → Prop) (M : GoInterfaceOk → Prop) (target : GoError) (l : Loc)
    (c : GoInterface) (hc : S c) :
    l.[fmt.wrapError, go!"err"] ↦□ c ∗ _root_.Perennial.errors.errorIsTree (GF := GF) S M target ⊢
      _root_.Perennial.errors.errorIsTree (GF := GF)
        (fun e => S e ∨ e = interface.mkOk (go.GoType.PointerType _root_.Perennial.fmt.wrapError.ty) #l)
        (fun ii => M ii ∧ interface.ok ii ≠ interface.mkOk (go.GoType.PointerType _root_.Perennial.fmt.wrapError.ty) #l)
        target := by
  obtain ⟨hIs, hU⟩ := (wrapError_methods (GF := GF) (hG := hG))
  iintro ⟨#Hc, #Htree⟩
  iintro !> %ii %hii
  by_cases hw : interface.ok ii = interface.mkOk (go.GoType.PointerType _root_.Perennial.fmt.wrapError.ty) #l
  · cases hw
    unfold _root_.Perennial.errors.errorWalkNode
    simp only [hIs, hU, reduceCtorEq, ↓reduceIte]
    isplitr
    · ipureintro; intro h; cases h
    iintro !> %Φ - HΦ
    wp_apply wp_wrapError_Unwrap l c $$ [Hc]
    · iexact Hc
    iapply HΦ
    ipureintro
    exact ⟨Or.inl hc, fun e he => by rw [List.mem_singleton.mp he]; exact Or.inl hc⟩
  · have hS : S (interface.ok ii) := hii.resolve_right hw
    ihave Hn := Htree $$ %ii %hS
    unfold _root_.Perennial.errors.errorWalkNode
    iNamed Hn
    isplitl []
    · by_cases hI : methodSet ii.ty !! go!"Is" = some (go.Signature [go.error] false [go.bool])
      · simp only [hI, ↓reduceIte]
        iintro !> %Φ - HΦ
        wp_apply HIs as %b %Hb
        iapply HΦ
        ipureintro
        exact fun hb => ⟨Hb hb, hw⟩
      · simp only [hI, ↓reduceIte]
        ipureintro; intro h; cases h
    by_cases h1 : methodSet ii.ty !! go!"Unwrap" = some (go.Signature [] false [go.error])
    · simp only [h1, ↓reduceIte]
      iintro !> %Φ - HΦ
      wp_apply HUnwrap as %e ⟨%He, %Hu⟩
      iapply HΦ
      ipureintro
      exact ⟨Or.inl He, fun e' he' => Or.inl (Hu e' he')⟩
    · by_cases h2 : methodSet ii.ty !! go!"Unwrap" =
          some (go.Signature [] false [go.GoType.SliceType go.error])
      · simp only [h1, ↓reduceIte]
        simp only [h2, ↓reduceIte]
        iintro !> %Φ - HΦ
        wp_apply HUnwrap as %s %dq %es ⟨Hs, %Hes, %Hu⟩
        iapply HΦ
        iframe
        ipureintro
        exact ⟨fun e he => Or.inl (Hes e he), fun e he => Or.inl (Hu e he)⟩
      · simp only [h1, h2, ↓reduceIte]
        ipureintro; intro _ h; cases h

/-- A `*fmt.wrapError` of `c` is typed as `c`'s tree, at a pointer target. -/
theorem wrap_treeTyped (S : GoError → Prop) (target : GoError) (l : Loc)
    (h : _root_.Perennial.errors.TreeTyped S target) :
    _root_.Perennial.errors.TreeTyped
      (fun e => S e ∨ e = interface.mkOk (go.GoType.PointerType _root_.Perennial.fmt.wrapError.ty) #l) target := by
  intro ii tii hii ht hty
  rcases hii with hii | hii
  · exact h ii tii hii ht hty
  · cases hii; exact ⟨l, rfl⟩

/-- An `*errors.errorString` is a target `fmt.ErrorfErrsNot.spec` admits: a pointer error, no `*fmt.wrapError`. -/
theorem errorString_target (x : Loc) :
    ∀ tii, interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x = interface.ok tii →
      _root_.Perennial.errors.IsPointerError tii ∧
      tii.ty ≠ go.GoType.PointerType _root_.Perennial.fmt.wrapError.ty := by
  intro tii h
  cases h
  refine ⟨⟨_, x, rfl, rfl⟩, ?_⟩
  rw [_root_.Perennial.fmt.wrapError_ty_eq]
  unfold _root_.Perennial.errors.errorString.ty
  simp

/-- **A `*fmt.wrapError` of `c`, not `t`**, has `c`'s `errTreeNot`. -/
theorem errTreeNot_wrapError (l : Loc) (c t : GoInterface)
    (hne : interface.mkOk (go.GoType.PointerType _root_.Perennial.fmt.wrapError.ty) #l ≠ t) :
    l.[fmt.wrapError, go!"err"] ↦□ c ∗ errTreeNot (GF := GF) c t ⊢
      errTreeNot (GF := GF) (interface.mkOk (go.GoType.PointerType _root_.Perennial.fmt.wrapError.ty) #l) t := by
  iintro ⟨#Hc, #Htr⟩
  unfold errTreeNot
  icases Htr with ⟨%hc, %S, %M, #Htree, %hS, %hty, %hno⟩
  isplitr
  · ipureintro; exact hne
  iexists _, _
  isplitl
  · iapply wrap_errorIsTree S M t l c hS
    iframe Hc Htree
  ipureintro
  refine ⟨Or.inr rfl, wrap_treeTyped S t l hty, fun ii hii => ?_⟩
  rcases hii with hii | hii
  · exact ⟨(hno ii hii).1, fun h => (hno ii hii).2 h.1⟩
  · exact ⟨fun h => hne (hii ▸ h), fun h => h.2 hii⟩

/-- **A `*fmt.wrapError` of `c`** has `c`'s `errTreeTerm`. -/
theorem errTreeTerm_wrapError (l : Loc) (c : GoInterface) :
    l.[fmt.wrapError, go!"err"] ↦□ c ∗ errTreeTerm (GF := GF) c ⊢
      errTreeTerm (GF := GF) (interface.mkOk (go.GoType.PointerType _root_.Perennial.fmt.wrapError.ty) #l) := by
  iintro ⟨#Hc, #Htr⟩
  unfold errTreeTerm
  iintro !> %u %hu
  ihave ⟨%S, %M, #Htree, %hS, %hty⟩ := Htr $$ %u %hu
  iexists _, _
  isplitl
  · iapply wrap_errorIsTree S M u l c hS
    iframe Hc Htree
  ipureintro
  exact ⟨Or.inr rfl, wrap_treeTyped S u l hty⟩

end wrap

end EtcdGrove
end Perennial
