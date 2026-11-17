/-
`apierrors.IsTooManyRequests(err)` (`k8s.io/apimachinery/pkg/api/errors`, names-only): whether the
error is a 429. **A named hypothesis, boundary pending approval** (one of the `apierrors`
predicates the reflector's `watch` calls; phase 4 of `notes/k8s-daemonset-plan.md`, fifth round):
`?` in `etc/link-lean-first-k8scache.txt`.

(apierrors-fix, 2026-11-17; `notes/apierrors-typednil-hypotheses.md`) Restated in place: the former
statement, some boolean with no precondition, was false: on a typed-nil `*StatusError`, bare or
wrapped, Go panics in `Status()` (`examples/axiomcx/apierrorstypednil` `TestTypedNil`). Now as
`IsTimeout`: precondition `apiErrOk err` (`View.lean`) or `nil` (the reflector's `list` asks of
the pager's error, `nil` on success; Go answers `false`, `errors.go:817-822`), and an answer every view of the error
agrees with: on `.status st _` whether the error's status has reason `TooManyRequests` or code 429 (`errors.go:725-739`: unlike the other checks, the code counts whatever the reason); on `.plain`, `false` (`reasonAndCodeForError` gives
`""`, `0`, `errors.go:817-822`).
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

/-- `apierrors.IsTooManyRequests(err)` of an error `apierrors`' checks may read: whether the error's status has reason `TooManyRequests` or code 429 (`errors.go:725-739`: unlike the other checks, the code counts whatever the reason); `false` on a `.plain` error (and on `nil`). -/
abbrev IsTooManyRequests.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors ∗
      (⌜err = interface.nil⌝ ∨ apiErrOk err) }}
    (App (Val (@! k8s_io.apimachinery.pkg.api.errors.IsTooManyRequests)) (Val #err))
  {{ (b : Bool), RET #b; □ ∀ w, apiErrAt err w -∗ ⌜b = match w with
      | .status st _ => decide (st.Reason' = go!"TooManyRequests") || decide (st.Code' = W32 429)
      | .plain => false⌝ }}

end spec

end apierrors
end EtcdGrove
end Perennial
