/-
Lean-first (no Rocq counterpart).

# What an `APIStatus` check sees of an error (stage 7e-2, `notes/k8s-7e-2-draft.md` §4.5, revised
after the attack, `notes/k8s-7e-2-attack.md` T1-T2)

`apierrors`' checks (`IsTimeout`, `HasStatusCause`, hence `storage.IsTooLargeResourceVersion`) read
an error only through `err.(APIStatus)` / `errors.As(err, &status)` and `Status()`
(`errors.go:96-109`, `:817-822`). Two views of an error decide them:

- `.status st cs`: a `*StatusError` with its status `st` (read-only) and, when its details are not
  `nil`, their causes `cs` (read-only; `[]` for `nil` details: `statusDetailsAt`);
- `.plain`: an error in which `errors.As` finds no `APIStatus`: `nil` or a leaf (`plainLeaf`: a
  dynamic type outside `APIStatus`'s type set and a leaf, `leafErrTy`: none of `Unwrap() error`,
  `Unwrap() []error`, `As(any) bool`, the three methods `errors.As` follows; the attack's `asErr`,
  `joinErr`), or a one-level wrapper: a dynamic type outside `APIStatus`'s type set with
  `Unwrap() error` (so not `Unwrap() []error`: a method set has one signature per name) and no
  `As(any) bool`, whose `Unwrap` returns, persistently (`□ WP`), `nil` or a leaf.

The wrapper case (k8s 7g, proposal V, `notes/k8s-7g-trust.md` §2; the checker passes
`*storage.StorageError`s, which have `Unwrap() error`) follows `errors/wrap.go`'s `As`: `nil` gives
`false`; a type outside `APIStatus` is not assignable to the target; no `As` method is asked; the
`Unwrap() error` case returns `false` on `nil` and otherwise loops on the result, a leaf, which is
neither assignable nor unwrapped. **The `□ WP` premise on `Unwrap` is where typed-nil receivers are
excluded** (M2 of the step 1 review): a typed nil pointer whose `Unwrap` dereferences it, or a struct
whose embedded pointer providing a promoted `Unwrap` is nil, panics in `Unwrap`, and no WP of that
call holds; so `errors.As`, hence every check over a `.plain` view, never reaches such a call. The
premise is persistent, so it holds at every call; it does not mean that `Unwrap` reads only
read-only state (a persistent WP can read mutable state through an invariant), but every result
it allows is `nil` or a leaf, and these all give the same answer. Go: `examples/k8s/etcd3/trustspecs_test.go`
`TestStatusChecksPlain` (nil, `*StorageError`s with inner `nil` or an `errors.New`, an `errors.New`,
a sentinel: every check false), `TestStorageErrorNotAPIStatus`, `TestPlainWrapperTypedNil` (a typed
nil `*StorageError`, bare or embedded nil, panics in `IsTimeout`, `HasStatusCause`,
`IsTooManyRequests`, `SuggestsClientDelay`; a non-nil wrapper of a leaf is false everywhere).

`timeoutV st` is `IsTimeout`'s test of a status (`errors.go:689-698`: reason `Timeout`, or an
unknown reason with code 504; `knownReasons`, the 19 of `errors.go:49-67`, without `""`),
`tooLargeV` is `IsTooLargeResourceVersion`'s, `tooLargeErrIs err` the error it recognizes.

The causes are a component of the view (`.status st cs`), not a function of the status: the status
holds only the details' address.
-/
module

public import Proof.k8s_io.apimachinery.pkg.api.errors.Init

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apierrors

open Iris Iris.BI

section pure
variable [GooseExts]

/-- **What an `APIStatus` check sees of an error** (see the file header). -/
inductive ApiErrView where
  | status (st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status)
      (cs : List k8s_io.apimachinery.pkg.apis.«meta».v1.StatusCause)
  | plain

/-- `IsTimeout`'s test of a status (`errors.go:689-698`). -/
def timeoutV (st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status) : Bool :=
  decide (st.Reason' = go!"Timeout") ||
    (!decide (st.Reason' ∈ knownReasons) && decide (st.Code' = W32 504))

/-- The causes list a cause of type `name`. -/
def causeIn (cs : List k8s_io.apimachinery.pkg.apis.«meta».v1.StatusCause) (name : GoString) : Bool :=
  decide (name ∈ cs.map (·.Type'))

/-- `IsTooLargeResourceVersion`'s answer on a view (`errors.go:259-265`). -/
def tooLargeV : ApiErrView → Bool
  | .status st cs => timeoutV st && causeIn cs go!"ResourceVersionTooLarge"
  | .plain => false

section leaf
variable [GoSemanticsFunctions] [go_gctx : GoGlobalContext]

/-- **A leaf error type** (revision after the attack, change 3): `errors.As` neither unwraps nor
asks it: its method set has none of `Unwrap() error`, `Unwrap() []error`, `As(any) bool`
(`errors/wrap.go`). -/
def leafErrTy (t : go.GoType) : Prop :=
  GoSemanticsFunctions.methodSet t !! go!"Unwrap" ≠ some (go.signature.Signature [] false [go.error]) ∧
  GoSemanticsFunctions.methodSet t !! go!"Unwrap" ≠
    some (go.signature.Signature [] false [go.GoType.SliceType go.error]) ∧
  GoSemanticsFunctions.methodSet t !! go!"As" ≠ some (go.signature.Signature [go.any] false [go.bool])

/-- **`errors.As` finds no `APIStatus` in `err` without unwrapping it**: `nil`, or a non-nil leaf
whose dynamic type is outside `APIStatus`'s type set. -/
def plainLeaf (err : GoInterface) : Prop :=
  err = interface.nil ∨ ∃ ii : GoInterfaceOk, err = GoInterface.ok ii ∧
    go.typeSetContains ii.ty k8s_io.apimachinery.pkg.api.errors.APIStatus.ty = false ∧
    leafErrTy ii.ty ∧ _root_.Perennial.errors.IsPointerError ii

end leaf

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

/-- `st.Details` is `nil` (and `cs` empty) or points (read-only) to details whose causes slice
holds (read-only) `cs`. -/
def statusDetailsAt (st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status)
    (cs : List k8s_io.apimachinery.pkg.apis.«meta».v1.StatusCause) : IProp GF :=
  iprop(⌜st.Details' = null ∧ cs = []⌝ ∨
    ∃ d : k8s_io.apimachinery.pkg.apis.«meta».v1.StatusDetails, st.Details' ↦□ d ∗ d.Causes' ↦*□ cs)

instance statusDetailsAt_persistent (st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status)
    (cs : List k8s_io.apimachinery.pkg.apis.«meta».v1.StatusCause) :
    Persistent (statusDetailsAt (GF := GF) st cs) := by
  unfold statusDetailsAt; infer_instance

/-- Details held read-only whose causes slice is `nil` (as `NewTimeoutError` makes them) have no
causes. -/
theorem statusDetailsAt_nil (st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status)
    (d : k8s_io.apimachinery.pkg.apis.«meta».v1.StatusDetails) (h : d.Causes' = slice.nil) :
    st.Details' ↦□ d ⊢ statusDetailsAt (GF := GF) st [] := by
  unfold statusDetailsAt
  iintro #Hd
  iright; iexists d; iframe Hd
  rw [h]
  iapply (ownSlice_nil (V := k8s_io.apimachinery.pkg.apis.«meta».v1.StatusCause) DFrac.discard)

/-- **The error `err` seen as the view `w`** (see the file header). -/
def apiErrAt (err : GoInterface) : ApiErrView → IProp GF
  | .status st cs => iprop(∃ l : Loc, ⌜err = interface.mkOk
        (go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty) #l⌝ ∗
      l ↦□ k8s_io.apimachinery.pkg.api.errors.StatusError.mk st ∗ statusDetailsAt st cs)
  | .plain => iprop(⌜plainLeaf err⌝ ∨ ∃ ii : GoInterfaceOk,
      ⌜err = GoInterface.ok ii ∧
        go.typeSetContains ii.ty k8s_io.apimachinery.pkg.api.errors.APIStatus.ty = false ∧
        GoSemanticsFunctions.methodSet ii.ty !! go!"Unwrap" =
          some (go.signature.Signature [] false [go.error]) ∧
        GoSemanticsFunctions.methodSet ii.ty !! go!"As" ≠
          some (go.signature.Signature [go.any] false [go.bool]) ∧
        _root_.Perennial.errors.IsPointerError ii⌝ ∗
      □ ∀ Φ : val → IProp GF, (∀ e : GoInterface, ⌜plainLeaf e⌝ -∗ Φ #e) -∗
          WP (App (Val #(methods ii.ty go!"Unwrap" ii.v)) (Val #())) {{ Φ }})

instance apiErrAt_persistent (err : GoInterface) (w : ApiErrView) :
    Persistent (apiErrAt (GF := GF) err w) := by
  cases w <;> unfold apiErrAt <;> (try unfold statusDetailsAt) <;> infer_instance

/-- **An error `apierrors`' checks may read** (the precondition of `IsTimeout`/`HasStatusCause`,
after the review of 2026-11-10: a typed-nil `*StatusError`, bare or wrapped with `%w`, panics in
`Status()`, `examples/k8s7e2attack/attack_test.go` `TestTypedNilStatusError`): a `*StatusError`
whose struct is held read-only (so non-nil), with its details (`statusDetailsAt`, read-only, so
every view of the error built later agrees on its causes: the fix of `HasStatusCause`,
`notes/hasstatuscause-later-view.md`), or a `.plain` error (`nil` included, since proposal V). A
view with its causes existential. -/
def apiErrOk (err : GoInterface) : IProp GF :=
  iprop((∃ (l : Loc) (st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status), ⌜err = interface.mkOk
      (go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty) #l⌝ ∗
      l ↦□ k8s_io.apimachinery.pkg.api.errors.StatusError.mk st ∗
      ∃ cs, statusDetailsAt st cs) ∨ apiErrAt err .plain)

instance apiErrOk_persistent (err : GoInterface) : Persistent (apiErrOk (GF := GF) err) := by
  unfold apiErrOk apiErrAt statusDetailsAt; infer_instance

/-- A view gives the precondition. -/
theorem apiErrAt_ok (err : GoInterface) (w : ApiErrView) :
    apiErrAt (GF := GF) err w ⊢ apiErrOk err := by
  cases w with
  | status st cs =>
    unfold apiErrOk apiErrAt
    iintro ⟨%l, %h, #Hl, #Hd⟩
    ileft; iexists l, st; isplitr
    · ipureintro; exact h
    · iframe Hl; iexists cs; iexact Hd
  | plain =>
    unfold apiErrOk
    iintro #H
    iright; iexact H

/-- **The store's too-large error (retry 0)**: `storage.NewTooLargeResourceVersionError(_, _, 0)`'s,
one `IsTooLargeResourceVersion` recognizes (`errors.go:259-265`): a timeout (`Timeout` reason)
`*StatusError` whose details list the `ResourceVersionTooLarge` cause, of code 504, its details held
read-only with `RetryAfterSeconds` 0 (so `SuggestsClientDelay` answers `false`). Not every error
`IsTooLargeResourceVersion` recognizes: the watcher's (`watchChan.startWatching`) and the cacher's
(`watchCache.waitUntilFreshLocked`) ask for a retry and are not this (k8s 7g, option (b1)). -/
def tooLargeErrIs (err : GoInterface) : IProp GF :=
  iprop(∃ st cs, apiErrAt err (.status st cs) ∗
    ⌜st.Reason' = go!"Timeout" ∧ go!"ResourceVersionTooLarge" ∈ cs.map (·.Type')⌝ ∗
    ∃ dv : k8s_io.apimachinery.pkg.apis.«meta».v1.StatusDetails, st.Details' ↦□ dv ∗
      ⌜st.Code' = W32 504 ∧ dv.RetryAfterSeconds' = W32 0⌝)

instance tooLargeErrIs_persistent (err : GoInterface) :
    Persistent (tooLargeErrIs (GF := GF) err) := by
  unfold tooLargeErrIs; infer_instance

/-- A too-large error is a `*StatusError` (the former post of `NewTooLargeResourceVersionError`). -/
theorem tooLargeErrIs_ptr (err : GoInterface) :
    tooLargeErrIs (GF := GF) err ⊢ ⌜∃ l : Loc, err = interface.mkOk
      (go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty) #l⌝ := by
  unfold tooLargeErrIs apiErrAt
  iintro ⟨%st, %cs, ⟨%l, %h, -⟩, -, -⟩
  ipureintro; exact ⟨l, h⟩

end defs

end apierrors
end EtcdGrove
end Perennial
