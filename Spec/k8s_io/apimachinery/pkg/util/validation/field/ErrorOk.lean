/-
`field.errorOk e`: `e` is a `*field.Error` whose `Error()` (translated with its body, as
`ErrorBody` and `ErrorType.String` are) `fmt` can call: a struct no one writes any more (read-only,
`↦□`) of a known error type, whose bad value is a string. What `ErrorList.ToAggregate` needs of each
error of its list (it formats each with `fmt.Sprintf("%v", err)`) and what the validators' error
lists hold (`field.Required`/`field.Invalid` of a string value, as `IsDomainPrefixedKey`'s).
Lean-first (no Rocq counterpart).
-/
module

public import GeneratedProof.k8s_io.apimachinery.pkg.util.validation.field
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace field

open Iris Iris.BI

/-- The error types `field` declares (`ErrorTypeNotFound`, ..., `ErrorTypeTooShort`): those
`ErrorBody` handles (another one would make it build an `InternalError`). -/
def knownErrorTypes : List GoString :=
  [go!"FieldValueNotFound", go!"FieldValueRequired", go!"FieldValueDuplicate",
   go!"FieldValueInvalid", go!"FieldValueNotSupported", go!"FieldValueForbidden",
   go!"FieldValueTooLong", go!"FieldValueTooMany", go!"FieldValueTooFew", go!"InternalError",
   go!"FieldValueTypeInvalid", go!"FieldValueTooShort"]

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.k8s_io.apimachinery.pkg.util.validation.field.Assumptions]

/-- **`e` is a `*field.Error` `fmt` can format** (see the file header): read-only, of a known
type, with a string as its bad value. Persistent. -/
def errorOk (e : Loc) : IProp GF :=
  iprop(∃ v : _root_.Perennial.k8s_io.apimachinery.pkg.util.validation.field.Error, e ↦□ v ∗
    ⌜v.Type' ∈ knownErrorTypes ∧ ∃ str : GoString, v.BadValue' = interface.mkOk go.string #str⌝)

instance errorOk_persistent (e : Loc) : Persistent (errorOk (GF := GF) e) := by
  unfold errorOk; infer_instance

end defs

end field
end EtcdGrove
end Perennial
