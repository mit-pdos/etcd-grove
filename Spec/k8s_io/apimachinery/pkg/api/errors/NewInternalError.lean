/-
`apierrors.NewInternalError` (`k8s.io/apimachinery/pkg/api/errors/errors.go`): a 500: the status `Failure`, reason `InternalError`, code 500. Proved over its body since prove-k8s3 (2026-11-21: Perennial's `fmt.Sprintf` model formats its message's `%v` of an error under `fmt.argsOk`); until then a trust-boundary axiom. Lean-first (no Rocq counterpart).

(prove-k8s3, 2026-11-21; `notes/specs-only/ledger.md`) The precondition also says that the error's
method set has `Error() string` (`fmt.noArgStringSig`), which Go's type system gives every non-nil
`error` (its dynamic type implements `error`) but the model does not (an interface value's type is
not tied to its static interface): `fmt`'s `%v` of it calls `Error()` because it is an `error`
(`handleMethods`' `case error`), which `fmt.argOk` states by that method-set entry.

(apierrors-fix, 2026-11-17; HasStatusCause fix (a), `notes/hasstatuscause-later-view.md`) The
post also gives the details, read-only, with one cause of type `""` (`statusDetailsAt st [c]`): Go
sets `Details` to a fresh `&StatusDetails{Causes: []StatusCause{{Message: err.Error()}}}`. And a
precondition, which the former statement lacked (it was false): Go calls `err.Error()` directly, so a
`nil` error, or one whose `Error()` panics, panics; the error is non-nil and its `Error()` returns
some string (`fmt.stringMethodSpec`, which `errors.New`'s and `fmt.Errorf`'s errors have). It has
no `Format` method (the attack of 2026-11-17, `notes/axiom-review/apierrors-fix.md`: the message's
`%v` calls `Format` in place of `Error()`, and `fmt` re-panics when the panic value's own `Error()`
panics, `print.go:591-594`, `630-634`). Go: `examples/premisefix/apierrorsdetails`
`TestNewInternalError`, `TestNestedPanics`.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.Defs
public import Proof.k8s_io.apimachinery.pkg.api.errors.View
public import Spec.fmt.Errorf

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace apierrors

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apimachinery.pkg.api.errors.Assumptions]

/-- `apierrors.NewInternalError(err)`, of a non-nil error without `Format` whose `Error() string` returns: a 500: the
status `Failure`, reason `InternalError`, code 500, with details holding one cause of type `""`
(see the file header). -/
abbrev NewInternalError.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors ∗
      ∃ ei : GoInterfaceOk, ⌜err = GoInterface.ok ei⌝ ∗ fmt.stringMethodSpec ei go!"Error" ∗
        ⌜methodSet ei.ty !! go!"Format" = none ∧
          methodSet ei.ty !! go!"Error" = some fmt.noArgStringSig⌝ }}
    (App (Val (@! k8s_io.apimachinery.pkg.api.errors.NewInternalError)) (Val #err))
  {{ (p : Loc), RET #p; ∃ (st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status)
      (c : k8s_io.apimachinery.pkg.apis.«meta».v1.StatusCause),
      p ↦ k8s_io.apimachinery.pkg.api.errors.StatusError.mk st ∗ statusDetailsAt st [c] ∗
      ⌜st.Status' = go!"Failure" ∧ st.Reason' = go!"InternalError" ∧ st.Code' = W32 500 ∧
        c.Type' = go!""⌝ }}

end spec

end apierrors
end EtcdGrove
end Perennial
