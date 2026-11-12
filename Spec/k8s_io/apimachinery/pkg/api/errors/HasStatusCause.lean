/-
`apierrors.HasStatusCause(err, name)` (`k8s.io/apimachinery/pkg/api/errors/errors.go:92-109`,
names-only): of a `*StatusError` whether its details list a cause of type `name`; of an error that is
no `APIStatus` and wraps none (`.plain`), `false`. Stated as a post every view of the error answers
(a caller holding no view, the pod control's create and the DaemonSet controller's `syncNodes`, sees
some bool, the former statement). Precondition `apiErrOk err` (`View.lean`): a `*StatusError` held
read-only, or a `.plain` error; added after the review of 2026-11-10, which refuted the
precondition-free statement: a typed-nil `*StatusError`, bare or wrapped with `%w`, panics in
`Status().Details` (`examples/k8s7e2attack/attack_test.go` `TestTypedNilStatusError`). The details
and their causes are read without being held (the pod control's create holds only the struct):
once non-nil, `Status().Details.Causes` cannot panic in Go.

Faithful: `StatusCause` reads the error only through `err.(APIStatus)` / `errors.As(err, &status)` and
`Status().Details.Causes` (`TestStatusView`, `TestPlainView`). The trust boundary: restated in stage
7e-2 (`notes/k8s-7e-2-draft.md` §5.1, attacked T2; Q7e-2-3: an axiom, where it was a named
hypothesis of the DaemonSet track, `?` in `etc/link-lean-first-k8sdaemon.txt`),
`Proof/k8s_io/apimachinery/pkg/api/errors/HasStatusCause.lean`. Lean-first (no Rocq counterpart).
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
abbrev HasStatusCause.spec : Prop :=
  ∀ (err : GoInterface) (name : k8s_io.apimachinery.pkg.apis.«meta».v1.CauseType),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors ∗ apiErrOk err }}
    (App (App (Val (@! k8s_io.apimachinery.pkg.api.errors.HasStatusCause)) (Val #err)) (Val #name))
  {{ (b : Bool), RET #b; □ ∀ w, apiErrAt err w -∗ ⌜b = match w with
      | .status _ cs => causeIn cs name | .plain => false⌝ }}

end spec

end apierrors
end EtcdGrove
end Perennial
