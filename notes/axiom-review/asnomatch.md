# `errors.AsNoMatch`: the new trust boundary of `errors.As` (prove-k8s2, 2026-11-20)

Checked against Go's source by its author (go1.27.3, the toolchain `etc/goose.py` pins:
`src/errors/wrap.go:102-160`), with Go tests; not attacked by the `axiom` skill.

## What changed

Out (5 axioms): `apierrors.IsTimeout`, `IsTooManyRequests`, `HasStatusCause`,
`SuggestsClientDelay` (now proved over their bodies, translated in `Code/k8s_io/apimachinery/pkg/api/
errors.toml`, with `StatusCause` and `reasonAndCodeForError`), and `errors.AsLeafTy` (now a theorem:
the leaf case of the new axiom). In (1): `errors.AsNoMatch.wp_proof` (`Spec/errors/AsNoMatch.lean`).
The package fact of `apimachinery/pkg/api/errors` went from `True` to `apierrorsInit` (`knownReasons`
holds, read-only, the map of the 19 known reasons; proved by its translated initializer), which
`IsTimeout`'s lookup reads.

## The statement

`errors.As(err, &v)`, with `AsTarget T` (`T` an interface or implementing `error`) and `l ↦ v` framed,
returns `false` and leaves `v` when `err` is

1. `nil`; or
2. a leaf (`isLeafError`: no `As(any) bool`, no `Unwrap() error`, no `Unwrap() []error`) whose dynamic
   type is outside `T`'s type set and, for a non-interface `T`, of another underlying type than `T`; or
3. a wrapper: dynamic type outside `T`'s type set (another underlying type for a non-interface `T`),
   `Unwrap() error` in its method set, no `As(any) bool`, with a WP of one call of its `Unwrap`
   whose result is `nil` or a leaf as in 2.

## Against the source

- `As` (`:102-119`): `err == nil` returns `false` before any check (1, and the `AsTarget` premise is
  then only stronger than needed). Otherwise the target checks: `nil` target or not a non-nil pointer
  panics (excluded: the target is `interface.mkOk (PointerType T) #l` with `l ↦ v`, so non-null);
  `*target` neither an interface nor implementing `error` panics (excluded by `AsTarget T`).
- `as` (`:121-160`), per iteration: (a) `reflectlite.TypeOf(err).AssignableTo(targetType)` stores and
  returns `true`. For an interface `T` assignability of a non-interface dynamic type is implementing
  `T` (type set: excluded). For a non-interface `T`: identical types, or identical underlying types
  with one of them unnamed, or a bidirectional channel type assignable to a channel `T` with one
  unnamed. Different underlying types exclude the first two; for the third, both are channel types
  with methods (the dynamic type implements `error`, `T` implements `error` by `AsTarget`), so both
  named, which the rule excludes. (b) `err.(interface{ As(any) bool })`: excluded by the method set.
  (c) the type switch: `Unwrap() error` calls it once, returns `false` on `nil`, else loops with the
  result; `Unwrap() []error`: excluded for leaves and for wrappers (a method set has one signature per
  name, and the wrapper's is `Unwrap() error`); default: `false`.
- A wrapper therefore calls exactly one method, its `Unwrap`, and then sees `nil` (false) or a leaf,
  which (a)-(c) answer `false` with no call. The target is written only in (a). `TypeOf`,
  `AssignableTo` and the assertions call no method of the error.
- Method sets: the premises read Goose's `methodSet`, which lists every method, promoted ones
  included (`MethodSetIs`), as `AsLeafTy`'s review relied on (etcd-grove-81, 2026-11-15). A wrapper
  whose `Unwrap` is promoted through a nil embedded pointer, or a typed-nil wrapper, panics in
  `Unwrap`: the WP premise is unprovable for it, so the axiom says nothing (as `View.lean`'s `□ WP`
  premise, `TestPlainWrapperTypedNil`).
- The WP is consumed once (not persistent): Go calls `Unwrap` once on this path.

## Go evidence

`examples/premisefix/watcherctx/asnomatch_test.go` (new): wrappers over `nil` and over an
`errors.New`, with an interface target (`APIStatus`, as the checks) and a pointer target: `false`,
the target unwritten, `Unwrap` called once; `nil`: `false`; negative: a wrapper of a `*StatusError`
is found. `asleafty_test.go` (the leaf case) and `examples/k8s/etcd3/trustspecs_test.go`
(`TestStatusChecksPlain`, `TestPlainWrapperTypedNil`) unchanged and passing.

## Not covered (deliberately)

Depth greater than one (a wrapper of a wrapper), `Unwrap() []error` trees, errors with an `As`
method, and a match: none is needed by a caller today; each would be a separate, reviewed extension
(Perennial's `errors.As.spec` allows any result for them).
