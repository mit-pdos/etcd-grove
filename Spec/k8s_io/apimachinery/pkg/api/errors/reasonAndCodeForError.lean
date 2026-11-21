/-
`apierrors.reasonAndCodeForError(err)` (`k8s.io/apimachinery/pkg/api/errors/errors.go:817-822`): the
reason and the code of the status `err` holds (`err.(APIStatus)`, else `errors.As(err, &status)`, then
`Status()`), else `("", 0)`. Of a `*StatusError` (view `.status st _`) its status's `Reason` and
`Code`; of a `.plain` error, `("", 0)`. Stated, as `IsTimeout.spec`, as a post every view of the error
answers, under `apiErrOk err` (a typed-nil `*StatusError` panics in `Status()`). `IsTimeout`'s and
`IsTooManyRequests`' callee (prove-k8s2, 2026-11-20). Lean-first.
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
abbrev reasonAndCodeForError.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors ∗ apiErrOk err }}
    (App (Val (@! k8s_io.apimachinery.pkg.api.errors.reasonAndCodeForError)) (Val #err))
  {{ (r : GoString) (c : w32), RET (PairV #r #c); □ ∀ w, apiErrAt err w -∗ ⌜match w with
      | .status st _ => r = st.Reason' ∧ c = st.Code'
      | .plain => r = go!"" ∧ c = W32 0⌝ }}

end spec

end apierrors
end EtcdGrove
end Perennial
