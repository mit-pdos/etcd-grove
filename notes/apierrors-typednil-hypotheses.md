---
title: apierrors.IsTooManyRequests/IsGone/IsInternalError/IsResourceExpired specs are false (typed nil *StatusError)
found: 2026-11-17
by: k8s 7g step 1 (IsTooManyRequests, notes/k8s-7g-trust.md on branch k8s-7g); soundness-1117 (the other three); Go test examples/axiomcx/apierrorstypednil
blocks-proof: no (named hypotheses, `?` in etc/link-lean-first-k8scache.txt; no closed theorem discharges them)
status: fixed on branch apierrors-fix (pre `nil` or `apiErrOk`, per-view posts), pending land
---
# Four `apierrors` hypotheses are false

A bug in this repository's specs, not in Kubernetes.

`Spec/k8s_io/apimachinery/pkg/api/errors/{IsTooManyRequests,IsGone,IsInternalError,IsResourceExpired}.lean`
state "some boolean" with no precondition. On a typed nil `*StatusError` (bare or wrapped) each panics
in Go: `ReasonForError`'s `err.(APIStatus)` succeeds and `(*StatusError).Status()` dereferences the
nil receiver: the flaw found for `IsTimeout` on 2026-11-10 (`examples/k8s7e2attack`
`TestTypedNilStatusError`). `examples/axiomcx/apierrorstypednil/apierrorstypednil_test.go`
(`TestTypedNil`: all four panic; the test passes).

**Reach.** Hypotheses of client-go cache's `Link` (`h_errors_*`): the linked results of the reflector
(`Reflector.watch`, `isWatchErrorRetriable`, `isExpiredError`, `ListPager.list`) are conditional on
false premises, so vacuous as stated. No axiom, no closed theorem.

**Fix, approved.** Each in place: precondition `apiErrOk err`, the answer per view (T for
`IsTooManyRequests`, `notes/k8s-7g-trust.md` on `k8s-7g`); `handleAnyWatch`'s post says its error is
`apiErrOk`; the reflector's call sites discharge it.
