# Requirements on `go.etcd.io/bbolt/errors` (batch 4c, with `S/bbolt/*.go`)

## from 4d

The package's `init`: each error variable of `bbolt/errors` (`ErrInvalid`, `ErrVersionMismatch`,
`ErrChecksum` at least) holds, read-only, a non-nil error value (`globalAddr g ↦□ e ∗
⌜e ≠ GoInterface.nil⌝`), as a law of the package (the shape of raft's `errs_init.spec`); pairwise
distinct if bbolt's clients compare them. Used by: `BboltCommon.Meta.Validate.spec` (its error is
the value of the variable `metaErr` names, not nil), and so `DB.Open`'s error path
(db.go:585-590).

## from 4c (answer)

Done in bbolt's own API (the errors package has no batch of its own): `Bbolt.errIs g e`
(`globalAddr g ↦□ e`), `Bbolt.isErr`, and the law `Bbolt.errIs_distinct.spec` (with
`isPkgInit` of `bbolt/errors`: each variable of `Bbolt.bboltErrNames`, which includes
`ErrInvalid`, `ErrVersionMismatch`, `ErrChecksum`, holds a non-nil value, pairwise distinct), in
`Spec/go_etcd_io/bbolt/Api.lean`.

## from I7 (integration: moved)

The answer above moved to the errors package's own API, `Spec/go_etcd_io/bbolt/errors/Api.lean`
(namespace `BboltErrors`: `errIs`, `isErr`, `bboltErrNames`, laws `errIs_init.spec`,
`errIs_distinct.spec`), because `internal/common` (a dependency of `bbolt`) uses it too:
`BboltCommon.Meta.Validate.spec`'s error is now `∃ g, ⌜metaErr v = some g⌝ ∗ BboltErrors.isErr g
err`. `Bbolt` re-exports the three names (`export BboltErrors (...)`), so `Bbolt.isErr` still
resolves.
