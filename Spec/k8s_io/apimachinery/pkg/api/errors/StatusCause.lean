/-
`apierrors.StatusCause(err, name)` (`k8s.io/apimachinery/pkg/api/errors/errors.go:99-109`): the first
cause of type `name` in the details of the status `err` holds (`err.(APIStatus)`, else
`errors.As(err, &status)`, then `Status().Details.Causes`), with `true`; else the zero cause and
`false`. Of a `*StatusError` (view `.status _ cs`) whether `cs` lists a cause of type `name`; of a
`.plain` error, `false`. Stated, as `HasStatusCause.spec` (its caller, prove-k8s2, 2026-11-20), as a
post every view of the error answers, under `apiErrOk err`; the cause itself is not stated (no caller
reads it). Lean-first.
-/
module

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

/-- See the file header. -/
abbrev StatusCause.spec : Prop :=
  ∀ (err : GoInterface) (name : k8s_io.apimachinery.pkg.apis.«meta».v1.CauseType),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors ∗ apiErrOk err }}
    (App (App (Val (@! k8s_io.apimachinery.pkg.api.errors.StatusCause)) (Val #err)) (Val #name))
  {{ (c : k8s_io.apimachinery.pkg.apis.«meta».v1.StatusCause) (b : Bool), RET (PairV #c #b);
      □ ∀ w, apiErrAt err w -∗ ⌜b = match w with
        | .status _ cs => causeIn cs name | .plain => false⌝ }}

end spec

end apierrors
end EtcdGrove
end Perennial
