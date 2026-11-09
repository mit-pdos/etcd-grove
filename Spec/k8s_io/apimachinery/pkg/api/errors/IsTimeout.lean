/-
`apierrors.IsTimeout(err)` (`k8s.io/apimachinery/pkg/api/errors/errors.go:689-698`, names-only): of
a `*StatusError` its status's timeout test (`timeoutV`: `reasonAndCodeForError`, `:817-822`, the
`APIStatus` assertion, then `Status()`, the struct's `ErrStatus`); of an error that is no `APIStatus`
and wraps none (`.plain`), `false` (reason `Unknown`, code 0). Stated as a post every view of the
error answers (a caller holding no view sees some bool).

Faithful: `IsTimeout` reads the error only through `err.(APIStatus)` / `errors.As(err, &status)` and
`Status()`, which for `*StatusError` returns `ErrStatus` (`errors.go:52-56`); for a value whose type
does not implement `APIStatus` and has no `Unwrap`/`As`, `errors.As` is false (`TestStatusView`,
`TestPlainView`, `TestLeafMustExcludeAsAndUnwrapSlice`). The trust boundary (stage 7e-2,
`notes/k8s-7e-2-draft.md` §5.1, attacked T1): an axiom,
`Proof/k8s_io/apimachinery/pkg/api/errors/IsTimeout.lean`. Lean-first (no Rocq counterpart).
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
abbrev IsTimeout.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors }}
    (App (Val (@! k8s_io.apimachinery.pkg.api.errors.IsTimeout)) (Val #err))
  {{ (b : Bool), RET #b; □ ∀ w, apiErrAt err w -∗ ⌜b = match w with
      | .status st _ => timeoutV st | .plain => false⌝ }}

end spec

end apierrors
end EtcdGrove
end Perennial
