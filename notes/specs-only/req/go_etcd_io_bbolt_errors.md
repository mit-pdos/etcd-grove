# Requirements on `go.etcd.io/bbolt/errors` (batch 4c, with `S/bbolt/*.go`)

## from 4d

The package's `init`: each error variable of `bbolt/errors` (`ErrInvalid`, `ErrVersionMismatch`,
`ErrChecksum` at least) holds, read-only, a non-nil error value (`globalAddr g ↦□ e ∗
⌜e ≠ GoInterface.nil⌝`), as a law of the package (the shape of raft's `errs_init.spec`); pairwise
distinct if bbolt's clients compare them. Used by: `BboltCommon.Meta.Validate.spec` (its error is
the value of the variable `metaErr` names, not nil), and so `DB.Open`'s error path
(db.go:585-590).
