/-
Lean-first (no Rocq counterpart).

# What the proofs of `apierrors`' `APIStatus` checks share (prove-k8s2, 2026-11-20)

`IsTimeout`, `IsTooManyRequests` (through `reasonAndCodeForError`), `HasStatusCause` (through
`StatusCause`) and `SuggestsClientDelay` all start with `status, ok := err.(APIStatus)` and
`ok || errors.As(err, &status)` (`errors.go:96-109`, `:791-805`, `:817-822`). Under `apiErrOk err`
(`View.lean`) the error is seen either as `.status st cs` (a `*StatusError`: the assertion holds and
`errors.As` is not called) or as `.plain` (the assertion fails, and `errors.As` returns `false`,
`errors.AsNoMatch`, the target unchanged: `wp_As_plain`). Every view of the error agrees with the one
the proof took (`apiErrAt_status_agree`, `apiErrAt_plain_agree`), which turns each check's answer on
one view into the post every view answers.
-/
module

public import Proof.k8s_io.apimachinery.pkg.api.errors.View
public import Spec.errors.AsNoMatch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apierrors

open Iris Iris.BI Iris.ProofMode

/-- A reason is in the map `knownReasons` holds iff it is one of the 19 known reasons. -/
theorem knownReasonsMap_lookup [GooseExts] (r : GoString) :
    (knownReasonsMap !! r).isSome = decide (r ∈ knownReasons) := by
  have key : ∀ (l : List GoString) (m : GMap GoString Unit),
      ((l.foldl (fun m r => <[r := ()]> m) m) !! r).isSome = (decide (r ∈ l) || (m !! r).isSome) := by
    intro l
    induction l with
    | nil => intro m; simp
    | cons a l ih =>
      intro m
      simp only [List.foldl_cons, ih, GMap.lookup_insert_eq_iff, List.mem_cons]
      by_cases h : a = r
      · subst h; simp
      · simp [h, show ¬ r = a from fun e => h e.symm]
  unfold knownReasonsMap
  rw [key]
  simp

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

/-- `*StatusError` implements `APIStatus` (its method set has `Status()`). -/
theorem statusErrorPtr_apiStatus :
    go.typeSetContains (go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty)
      k8s_io.apimachinery.pkg.api.errors.APIStatus.ty = true := by
  go_type_set

/-- `APIStatus` is an interface type. -/
theorem apiStatus_isInterface :
    go.isInterfaceType (underlying k8s_io.apimachinery.pkg.api.errors.APIStatus.ty) = true := by
  rw [go.is_underlying (t := k8s_io.apimachinery.pkg.api.errors.APIStatus.ty)]
  rfl

/-- `&status`, a `*APIStatus`, is a target `errors.As` accepts. -/
theorem apiStatus_asTarget :
    _root_.Perennial.errors.AsTarget k8s_io.apimachinery.pkg.api.errors.APIStatus.ty := by
  left
  rw [go.is_underlying (t := k8s_io.apimachinery.pkg.api.errors.APIStatus.ty)]
  exact ⟨_, rfl⟩

/-- An error `errors.As` finds no `APIStatus` in without unwrapping it ends `As`'s walk. -/
theorem plainLeaf_noMatch (e : GoInterface) (h : plainLeaf e) :
    errors.asNoMatchLeaf k8s_io.apimachinery.pkg.api.errors.APIStatus.ty e := by
  rcases h with h | ⟨ii, hii, hts, hl, hp⟩
  · exact Or.inl h
  · obtain ⟨X, p, hty, hv⟩ := hp
    refine Or.inr ⟨ii, hii, ⟨hl.2.2, hl.1, hl.2.1⟩, hts,
      by rw [hty]; exact _root_.Perennial.errors.asModelled_pointer X, fun _ => ⟨X, p, hty, hv⟩,
      fun h => ?_⟩
    rw [apiStatus_isInterface] at h
    cases h

/-- A `.plain` error is `nil`, or an error whose dynamic type is outside `APIStatus`'s type set. -/
theorem apiErrAt_plain_shape (err : GoInterface) :
    apiErrAt (GF := GF) err .plain ⊢ ⌜err = interface.nil ∨ ∃ ii : GoInterfaceOk,
      err = GoInterface.ok ii ∧
      go.typeSetContains ii.ty k8s_io.apimachinery.pkg.api.errors.APIStatus.ty = false⌝ := by
  unfold apiErrAt plainLeaf
  iintro (%h | ⟨%ii, %h, -⟩)
  · ipureintro
    rcases h with h | ⟨ii, hii, hts, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨ii, hii, hts⟩
  · ipureintro
    exact Or.inr ⟨ii, h.1, h.2.1⟩

/-- A `.plain` error is no `*StatusError`. -/
theorem apiErrAt_plain_ne (err : GoInterface) :
    apiErrAt (GF := GF) err .plain ⊢ ⌜∀ l : Loc, err ≠ interface.mkOk
      (go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty) #l⌝ := by
  iintro #H
  ihave %h := apiErrAt_plain_shape err $$ H
  ipureintro
  intro l hl
  subst hl
  rcases h with h | ⟨ii, hii, hts⟩
  · cases h
  · cases hii
    rw [statusErrorPtr_apiStatus] at hts
    cases hts

/-- **Every view of an error seen as `.status st cs` is that view** (the struct and the details are
held read-only). -/
theorem apiErrAt_status_agree (err : GoInterface) (st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status)
    (cs : List k8s_io.apimachinery.pkg.apis.«meta».v1.StatusCause) :
    apiErrAt (GF := GF) err (.status st cs) ⊢
      □ ∀ w, apiErrAt err w -∗ ⌜w = .status st cs⌝ := by
  iintro #H !> %w #Hw
  cases w with
  | plain =>
    ihave %hne := apiErrAt_plain_ne err $$ Hw
    iunfold apiErrAt at H
    icases H with ⟨%l, %hl, -⟩
    ipureintro
    exact absurd hl (hne l)
  | status st' cs' =>
    iunfold apiErrAt at H Hw
    icases H with ⟨%l, %hl, #Hl, #Hd⟩
    icases Hw with ⟨%l', %hl', #Hl', #Hd'⟩
    have hll : l' = l := by
      rw [hl] at hl'
      simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at hl'
      exact go.intoVal_inj hl'.symm
    subst hll
    icombine Hl Hl' gives %hst
    obtain rfl : st = st' := by injection hst
    iunfold statusDetailsAt at Hd Hd'
    icases Hd with (%hd | ⟨%d, #Hdp, #Hcs⟩) <;> icases Hd' with (%hd' | ⟨%d', #Hdp', #Hcs'⟩)
    · ipureintro
      rw [hd.2, hd'.2]
    · icases typedPointsto_not_null _ _ _ $$ Hdp' with %hnn
      ipureintro
      exact absurd hd.1 hnn
    · icases typedPointsto_not_null _ _ _ $$ Hdp with %hnn
      ipureintro
      exact absurd hd'.1 hnn
    · icombine Hdp Hdp' gives %hdd
      subst hdd
      icombine Hcs Hcs' gives %hcs
      ipureintro
      rw [hcs]

/-- **Every view of an error seen as `.plain` is `.plain`.** -/
theorem apiErrAt_plain_agree (err : GoInterface) :
    apiErrAt (GF := GF) err .plain ⊢ □ ∀ w, apiErrAt err w -∗ ⌜w = .plain⌝ := by
  iintro #H !> %w #Hw
  cases w with
  | plain => ipureintro; rfl
  | status st cs =>
    ihave %hne := apiErrAt_plain_ne err $$ H
    iunfold apiErrAt at Hw
    icases Hw with ⟨%l, %hl, -⟩
    ipureintro
    exact absurd hl (hne l)

/-- `apiErrOk` is one of the two views. -/
theorem apiErrOk_cases (err : GoInterface) :
    apiErrOk (GF := GF) err ⊢
      (∃ st cs, apiErrAt err (.status st cs)) ∨ apiErrAt err .plain := by
  unfold apiErrOk
  iintro (⟨%l, %st, %h, #Hl, %cs, #Hd⟩ | #H)
  · ileft
    iexists st, cs
    unfold apiErrAt
    iexists l
    isplitr
    · ipureintro; exact h
    · iframe Hl; iexact Hd
  · iright
    iexact H

/-- **`errors.As(err, &status)` of a `.plain` error**: `false`, `status` unchanged
(`errors.AsNoMatch`: a leaf or `nil` ends the walk; a wrapper's `Unwrap` returns one). -/
theorem wp_As_plain (wp_AsNoMatch : errors.AsNoMatch.spec (GF := GF) (hG := hG))
    (err : GoInterface) (l : Loc) (v : GoInterface) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ apiErrAt err .plain ∗ l ↦ v }}
      (App (App (Val (@! _root_.Perennial.errors.As)) (Val #err))
        (Val #(interface.mkOk (go.PointerType k8s_io.apimachinery.pkg.api.errors.APIStatus.ty) #l)))
    {{ RET #false; l ↦ v }} := by
  iintro %Φ ⟨#Hpkg, #Hpl, Hl⟩ HΦ
  have hk := _root_.Perennial.errors.asTargetKind_interface apiStatus_isInterface
  iapply (wp_AsNoMatch err l v apiStatus_asTarget hk.1 hk.2) $$ [Hl] HΦ
  iframe Hpkg Hl
  iunfold apiErrAt at Hpl
  icases Hpl with (%hleaf | ⟨%ii, %h, #HU⟩)
  · ileft
    ipureintro
    exact plainLeaf_noMatch err hleaf
  · iright
    unfold errors.asNoMatchWrap
    iexists ii
    isplitr
    · ipureintro
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      obtain ⟨X, p, hty, hv⟩ := h5
      refine ⟨h1, h2, by rw [hty]; exact _root_.Perennial.errors.asModelled_pointer X,
        fun _ => ⟨X, p, hty, hv⟩, fun hi => ?_, h4, h3⟩
      rw [apiStatus_isInterface] at hi
      cases hi
    · iintro %Φ' HΦ'
      iapply HU
      iintro %e %he
      iapply HΦ'
      ipureintro
      exact plainLeaf_noMatch e he

end lemmas

end apierrors
end EtcdGrove
end Perennial
