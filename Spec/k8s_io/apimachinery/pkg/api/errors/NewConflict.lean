/-
`apierrors.NewConflict` (`k8s.io/apimachinery/pkg/api/errors/errors.go`): a 409: the status `Failure`, reason `Conflict`, code 409. The trust boundary: its message formats an error (`%v`), which Perennial's `fmt.Sprintf` model does not cover; names only. Lean-first (no Rocq counterpart).

(apierrors-fix, 2026-11-17; HasStatusCause fix (a), `notes/hasstatuscause-later-view.md`) The
post also gives the details, read-only, with no causes (`statusDetailsAt st []`): Go sets `Details`
to a fresh `&StatusDetails{Group, Kind, Name}`, whose `Causes` is `nil`. No precondition: it never
calls `err.Error()` itself, and `fmt`'s `%v` recovers a panicking `Error` (and prints a `nil`
error). Go: `examples/premisefix/apierrorsdetails` `TestNewConflict`.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.Defs
public import Proof.k8s_io.apimachinery.pkg.api.errors.View

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

/-- `apierrors.NewConflict(...)`: a 409: the status `Failure`, reason `Conflict`, code 409, with
details and no causes (see the file header). -/
abbrev NewConflict.spec : Prop :=
  ∀ (gr : k8s_io.apimachinery.pkg.runtime.schema.GroupResource) (name : GoString) (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors }}
    (App (App (App (Val (@! k8s_io.apimachinery.pkg.api.errors.NewConflict)) (Val #gr)) (Val #name)) (Val #err))
  {{ (p : Loc), RET #p; ∃ st : k8s_io.apimachinery.pkg.apis.«meta».v1.Status, p ↦ k8s_io.apimachinery.pkg.api.errors.StatusError.mk st ∗
      statusDetailsAt st [] ∗
      ⌜st.Status' = go!"Failure" ∧ st.Reason' = go!"Conflict" ∧ st.Code' = W32 409⌝ }}

end spec

end apierrors
end EtcdGrove
end Perennial
