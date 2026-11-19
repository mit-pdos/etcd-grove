/-
`validation.IsDomainPrefixedKey(fldPath, key)` (apimachinery, names only): **the trust boundary**.
Some error list, each error `field.errorOk` (2026-11-19: what `field.ErrorList.ToAggregate`, now
proved, needs of its list: the errors are `field.Required(fldPath, "")`/`field.Invalid(fldPath,
key, msg)`, fresh `*field.Error`s of known types with string bad values, never written after).
Lean-first (no Rocq counterpart).
-/
module

public import GeneratedProof.k8s_io.apimachinery.pkg.util.validation
public import Spec.k8s_io.apimachinery.pkg.util.validation.field.ErrorOk

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace validation

open Iris Iris.BI 

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : _root_.Perennial.k8s_io.apimachinery.pkg.util.validation.field.Assumptions]

/-- See the file header. -/
abbrev IsDomainPrefixedKey.spec : Prop :=
  ∀ (fp : Loc) (key : GoString),
  {{ (True : IProp GF) }}
    (App (App (Val (@! _root_.Perennial.k8s_io.apimachinery.pkg.util.validation.IsDomainPrefixedKey))
      (Val #fp)) (Val #key))
  {{ (s : GoSlice), RET #s; ∃ errs : List Loc, s ↦* errs ∗ [∗list] e ∈ errs, field.errorOk e }}

end spec

end validation
end EtcdGrove
end Perennial
