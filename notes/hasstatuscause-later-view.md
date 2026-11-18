---
title: apierrors.HasStatusCause.wp_proof is false (a view built after the call)
found: 2026-11-17
by: the k8s 7g step-1 attack (notes/axiom-review/k8s-7g-trust.md on branch k8s-7g); Go test examples/axiomcx/hasstatuscause
blocks-proof: no (refuted as stated; its callers, RealPodControl.createPods and storage.IsTooLargeResourceVersion, do not write the details after the call)
status: fixed on branch apierrors-fix (fix (a)), pending land
---
# `HasStatusCause.wp_proof` is false

A bug in this repository's trust base, not in Kubernetes.

The axiom (`Proof/k8s_io/apimachinery/pkg/api/errors/HasStatusCause.lean`) takes `apiErrOk err`, which
holds a `*StatusError`'s struct read-only but not its details, and posts `□ ∀ w, apiErrAt err w -∗
⌜b = match w with | .status _ cs => causeIn cs name | .plain => false⌝`: a fact about every view of
the error, built at any later time. A caller that still owns the `*StatusDetails` writes their causes
after the call, persists them, builds `.status st [{Type: "X"}]` and concludes `b = true`; Go
returned `false`. `examples/axiomcx/hasstatuscause/hasstatuscause_test.go` (`TestLaterView`: the
program panics in Go; the test passes). The header's sentence "the details and their causes are read
without being held" is what fails.

**Reach.** Collections `k8s.txt`, `k8setcd3.txt` list the axiom; the DaemonSet controller's
`createPods` and `storage.IsTooLargeResourceVersion` use it.

**Fix (a), approved.** `apiErrOk`'s `*StatusError` branch also holds `statusDetailsAt st cs`, so any
later view agrees; `createPods` holds it through the apimodel's `errIs`, from stronger posts of the
`apierrors.New*` specs (two of them axioms: `NewConflict`, `NewInternalError`, their texts reviewed
before use).
