/-
`apierrors.IsGone(err)` (`k8s.io/apimachinery/pkg/api/errors`, names-only): whether the error's
status reason is `Gone`. **A named hypothesis, boundary pending approval** (one of the `apierrors`
predicates the reflector calls, through `isExpiredError`; phase 4 of `notes/k8s-daemonset-plan.md`,
fifth round): `?` in `etc/link-lean-first-k8scache.txt`.

(apierrors-fix, 2026-11-17; `notes/apierrors-typednil-hypotheses.md`) Restated in place: the former
statement, some boolean with no precondition, was false: on a typed-nil `*StatusError`, bare or
wrapped, Go panics in `Status()` (`examples/axiomcx/apierrorstypednil` `TestTypedNil`). Now as
`IsTimeout`: precondition `apiErrOk err` (`View.lean`) or `nil` (the reflector's `list` asks of
the pager's error, `nil` on success; Go answers `false`, `errors.go:817-822`), and an answer every view of the error
agrees with: on `.status st _` whether the error's status has reason `Gone`, or an unknown reason and code 410 (`errors.go:574-583`); on `.plain`, `false` (`reasonAndCodeForError` gives
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

/-- `apierrors.IsGone(err)` of an error `apierrors`' checks may read: whether the error's status has reason `Gone`, or an unknown reason and code 410 (`errors.go:574-583`); `false` on a `.plain` error (and on `nil`). -/
abbrev IsGone.spec : Prop :=
  ∀ (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.api.errors ∗
      (⌜err = interface.nil⌝ ∨ apiErrOk err) }}
    (App (Val (@! k8s_io.apimachinery.pkg.api.errors.IsGone)) (Val #err))
  {{ (b : Bool), RET #b; □ ∀ w, apiErrAt err w -∗ ⌜b = match w with
      | .status st _ => decide (st.Reason' = go!"Gone") ||
          (!decide (st.Reason' ∈ knownReasons) && decide (st.Code' = W32 410))
      | .plain => false⌝ }}

end spec

end apierrors
end EtcdGrove
end Perennial
