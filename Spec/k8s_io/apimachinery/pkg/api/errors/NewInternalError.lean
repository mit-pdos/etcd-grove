/-
`apierrors.NewInternalError` (`k8s.io/apimachinery/pkg/api/errors/errors.go`): a 500: the status `Failure`, reason `InternalError`, code 500. The trust boundary: its message formats an error (`%v`), which Perennial's `fmt.Sprintf` model does not cover; names only. Lean-first (no Rocq counterpart).

(apierrors-fix, 2026-11-17; HasStatusCause fix (a), `notes/hasstatuscause-later-view.md`) The
post also gives the details, read-only, with one cause of type `""` (`statusDetailsAt st [c]`): Go
sets `Details` to a fresh `&StatusDetails{Causes: []StatusCause{{Message: err.Error()}}}`. And a
precondition, which the former statement lacked (it was false): Go calls `err.Error()` directly, so a
`nil` error, or one whose `Error()` panics, panics; the error is non-nil and its `Error()` returns
some string (`fmt.stringMethodSpec`, which `errors.New`'s and `fmt.Errorf`'s errors have). Go:
`examples/premisefix/apierrorsdetails` `TestNewInternalError`.
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

/-- `apierrors.NewInternalError(err)`, of a non-nil error whose `Error()` returns: a 500: the
status `Failure`, reason `InternalError`, code 500, with details holding one cause of type `""`
(see the file header). -/
abbrev NewInternalError.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors ∗
      ∃ ei : GoInterfaceOk, ⌜err = GoInterface.ok ei⌝ ∗ fmt.stringMethodSpec ei go!"Error" }}
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
