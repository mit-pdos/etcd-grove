/-
Lean-first (no Rocq counterpart).

# What an `APIStatus` check sees of an error (stage 7e-2, `notes/k8s-7e-2-draft.md` §4.5, revised
after the attack, `notes/k8s-7e-2-attack.md` T1-T2)

`apierrors`' checks (`IsTimeout`, `HasStatusCause`, hence `storage.IsTooLargeResourceVersion`) read
an error only through `err.(APIStatus)` / `errors.As(err, &status)` and `Status()`
(`errors.go:96-109`, `:817-822`). Two views of an error decide them:

- `.status st cs`: a `*StatusError` with its status `st` (read-only) and, when its details are not
  `nil`, their causes `cs` (read-only; `[]` for `nil` details: `statusDetailsAt`);
- `.plain`: an error that neither is nor wraps an `APIStatus`: its dynamic type is outside
  `APIStatus`'s type set and is a leaf (`leafErrTy`: none of `Unwrap() error`, `Unwrap() []error`,
  `As(any) bool`, the three methods `errors.As` follows; the attack's `asErr`, `joinErr`).

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

/-- `errors.go:49-67`'s `knownReasons` (`StatusReasonUnknown`, `""`, is commented out there). -/
def knownReasons : List GoString :=
  [go!"Unauthorized", go!"Forbidden", go!"NotFound", go!"AlreadyExists", go!"Conflict",
   go!"Gone", go!"Invalid", go!"ServerTimeout", go!"StorageReadError", go!"Timeout",
   go!"TooManyRequests", go!"BadRequest", go!"MethodNotAllowed", go!"NotAcceptable",
   go!"RequestEntityTooLarge", go!"UnsupportedMediaType", go!"InternalError", go!"Expired",
   go!"ServiceUnavailable"]

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
variable [GoSemanticsFunctions]

/-- **A leaf error type** (revision after the attack, change 3): `errors.As` neither unwraps nor
asks it: its method set has none of `Unwrap() error`, `Unwrap() []error`, `As(any) bool`
(`errors/wrap.go`). -/
def leafErrTy (t : go.GoType) : Prop :=
  GoSemanticsFunctions.methodSet t !! go!"Unwrap" ≠ some (go.signature.Signature [] false [go.error]) ∧
  GoSemanticsFunctions.methodSet t !! go!"Unwrap" ≠
    some (go.signature.Signature [] false [go.GoType.SliceType go.error]) ∧
  GoSemanticsFunctions.methodSet t !! go!"As" ≠ some (go.signature.Signature [go.any] false [go.bool])

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

/-- **The error `err` seen as the view `w`** (see the file header). -/
def apiErrAt (err : GoInterface) : ApiErrView → IProp GF
  | .status st cs => iprop(∃ l : Loc, ⌜err = interface.mkOk
        (go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty) #l⌝ ∗
      l ↦□ k8s_io.apimachinery.pkg.api.errors.StatusError.mk st ∗ statusDetailsAt st cs)
  | .plain => iprop(⌜∃ ii : GoInterfaceOk, err = GoInterface.ok ii ∧
      go.typeSetContains ii.ty k8s_io.apimachinery.pkg.api.errors.APIStatus.ty = false ∧
      leafErrTy ii.ty⌝)

instance apiErrAt_persistent (err : GoInterface) (w : ApiErrView) :
    Persistent (apiErrAt (GF := GF) err w) := by
  cases w <;> unfold apiErrAt <;> (try unfold statusDetailsAt) <;> infer_instance

/-- **The error `IsTooLargeResourceVersion` recognizes** (`errors.go:259-265`): a timeout (`Timeout`
reason) `*StatusError` whose details list the `ResourceVersionTooLarge` cause. -/
def tooLargeErrIs (err : GoInterface) : IProp GF :=
  iprop(∃ st cs, apiErrAt err (.status st cs) ∗
    ⌜st.Reason' = go!"Timeout" ∧ go!"ResourceVersionTooLarge" ∈ cs.map (·.Type')⌝)

instance tooLargeErrIs_persistent (err : GoInterface) :
    Persistent (tooLargeErrIs (GF := GF) err) := by
  unfold tooLargeErrIs; infer_instance

/-- A too-large error is a `*StatusError` (the former post of `NewTooLargeResourceVersionError`). -/
theorem tooLargeErrIs_ptr (err : GoInterface) :
    tooLargeErrIs (GF := GF) err ⊢ ⌜∃ l : Loc, err = interface.mkOk
      (go.GoType.PointerType k8s_io.apimachinery.pkg.api.errors.StatusError.ty) #l⌝ := by
  unfold tooLargeErrIs apiErrAt
  iintro ⟨%st, %cs, ⟨%l, %h, -⟩, -⟩
  ipureintro; exact ⟨l, h⟩

end defs

end apierrors
end EtcdGrove
end Perennial
