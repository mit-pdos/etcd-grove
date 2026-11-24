/-
`apierrors.NewConflict` (`k8s.io/apimachinery/pkg/api/errors/errors.go`): a 409: the status `Failure`, reason `Conflict`, code 409. Proved over its body since prove-k8s2 (2026-11-21: Perennial's `fmt.Sprintf` model now formats its message's `%v` of an error under `fmt.argsOk`); until then a trust-boundary axiom. Lean-first (no Rocq counterpart).

(apierrors-fix, 2026-11-17; HasStatusCause fix (a), `notes/hasstatuscause-later-view.md`) The
post also gives the details, read-only, with no causes (`statusDetailsAt st []`): Go sets `Details`
to a fresh `&StatusDetails{Group, Kind, Name}`, whose `Causes` is `nil`. And a precondition, which
the former statement lacked (it was false; the attack of 2026-11-17,
`notes/axiom-review/apierrors-fix.md`): the message formats `err` with `%v`, and `fmt` calls its
`Format` in place of `Error()` when it has one, and re-panics when the panic value's own `Error()`
panics (`print.go:591-594`, `630-634`), so `err` is `nil` or an error without `Format` whose `Error()`
returns (`fmtErrorOkOrNil`; until 2026-11-24 `fmt.argOk`, which also admitted the predeclared basic
types, outside real `fmt`'s verified subset under `%v` of a named type: ledger 2026-11-24). Go: `examples/premisefix/apierrorsdetails` `TestNewConflict`,
`TestNestedPanics`.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.Defs
public import Proof.k8s_io.apimachinery.pkg.api.errors.View
public import Spec.fmt.Errorf
public import Spec.fmt.ErrorOk

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

/-- `apierrors.NewConflict(gr, name, err)`, of an `err` `fmt` prints without panicking: a 409: the
status `Failure`, reason `Conflict`, code 409, with details and no causes (see the file header). -/
abbrev NewConflict.spec : Prop :=
  ∀ (gr : k8s_io.apimachinery.pkg.runtime.schema.GroupResource) (name : GoString) (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors ∗ fmtErrorOkOrNil err }}
    (App (App (App (Val (@! k8s_io.apimachinery.pkg.api.errors.NewConflict)) (Val #gr)) (Val #name)) (Val #err))
  {{ (p : Loc), RET #p; ∃ st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status, p ↦ k8s_io.apimachinery.pkg.api.errors.StatusError.mk st ∗
      statusDetailsAt st [] ∗
      ⌜st.Status' = go!"Failure" ∧ st.Reason' = go!"Conflict" ∧ st.Code' = W32 409⌝ }}

end spec

end apierrors
end EtcdGrove
end Perennial
