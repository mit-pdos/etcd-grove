---
title: apierrors.NewConflict.wp_proof and NewInternalError.wp_proof are false (no precondition on the error)
found: 2026-11-17
by: apierrors-fix (NewInternalError, writing its new text) and etcd-grove-03's attack (NewConflict; notes/axiom-review/apierrors-fix.md)
blocks-proof: no (the callers pass errors.New errors and kErrOk errors, which meet the fix's preconditions)
status: fixed on branch apierrors-fix (preconditions fmt.argOk err / non-nil, Error() returns, no Format)
---
# `NewConflict.wp_proof` and `NewInternalError.wp_proof` are false

A bug in this repository's trust base, not in Kubernetes. Both axioms
(`Proof/k8s_io/apimachinery/pkg/api/errors/{NewConflict,NewInternalError}.lean`) had no precondition
on the error argument.

- `NewInternalError(err)` calls `err.Error()` directly (`errors.go:393`): a `nil` error, or one
  whose `Error()` panics, panics.
- Both format `err` with `%v` (`errors.go:242`, `:395`). `fmt` calls `Format` in place of `Error()`
  when the type has one (`fmt/print.go:630-634`), and re-panics when a recovered panic value's own
  `Error()` panics (`print.go:591-594`). So an error whose `Error()` (or `Format`) panics that way
  makes both panic.

Go: `examples/premisefix/apierrorsdetails` (`TestNewInternalError`, `TestNestedPanics`).

**Reach.** Collections `k8s.txt` and the daemonset ones list the axioms; the callers
(`transformErrorToEvent`, the daemonset apimodel's server) pass errors that meet the fix's
preconditions, so no result is known to be affected beyond resting on a false axiom.
