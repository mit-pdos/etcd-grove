# A premise Go's type system gives every caller (`apierrors.NewInternalError`, 2026-11-21)

`apierrors.NewInternalError(err)` was a trust-boundary axiom. Proving it over its body
(`fmt.Sprintf("Internal error occurred: %v", err)`) reaches Perennial's `fmt.argOk`, which asks, for
`%v` to call `Error()`, the method-set entry `methodSet ei.ty !! "Error" = some fmt.noArgStringSig`
(`fmt`'s `handleMethods`, `case error:`). Go's type system gives that entry to every non-nil `error`;
the model does not tie an interface value's dynamic type to its static interface.

## The first version

Precondition: the package initialized; `err` non-nil, `fmt.stringMethodSpec ei "Error"` (its
`Error()` returns a string), no `Format` method. Post: the `*StatusError` (500, `InternalError`, one
cause). Not provable: `argOk` needs the method-set entry, which nothing in the precondition gives.

## The change, and the review

Add the entry to the precondition's pure conjunct. It strengthens a premise callers see, which the
proving brief forbids by default; the agent flagged it instead of keeping the axiom. Callers:
`transformErrorToEvent` already had it (from `kErrOk`); the model API server's `apimodelInit` gained
the conjunct for its `errors.New` errors. The user approved: the premise makes sense.

## The approved spec

`Spec/k8s_io/apimachinery/pkg/api/errors/NewInternalError.lean`: the first version's precondition
plus `methodSet ei.ty !! go!"Error" = some fmt.noArgStringSig`; the post unchanged.

## What it shows

- A premise that Go's type system makes true of every value the caller can pass (here: an `error`'s
  dynamic type has `Error() string`) is not a weakening of the spec: it restates in the model a fact
  the model does not track. Add it rather than keep an axiom, say why in the spec's header, and give
  each caller's source for it. A premise that excludes values Go allows is different: that needs a
  ledger entry with evidence that no caller passes them.
