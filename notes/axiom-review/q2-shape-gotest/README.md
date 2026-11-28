# Q2 widening: requests outside `auth.reqShape` with auth on (2026-11-27)

Two tests, copied into the etcd fork at `8c28a4296` (the WAL pin, whose `server/auth` and `pkg/adt` are
etcd's), go1.27.3; output in `test-output.txt`:

- `q2_shape_test.go` (`tests/integration`): user `alice` may read and write the key `p` only. A writing
  transaction whose compare range is empty (`[a,a)`) or inverted (`[e,b)`), or that nests a get of `[a,a)`,
  with a put of `p` in each branch, is refused (`permission denied`); so is a delete of `[e,b)`. `p` stays
  absent, the revision unchanged. The model's verdict `kvGranted` grants all four: `auth.covers` of a range
  is `coversRange`, vacuous over an empty `[key, end)`.
- `q2_contains_test.go` (`pkg/adt`): the interval tree's `Contains`, which `checkKeyInterval` asks, answers
  `false` for these queries, and for an inverted query its answer depends on the tree's shape (the same two
  intervals inserted in the two orders give `false` and `true`): `Interval.Compare` of an inverted query
  is a stab at its begin, and `visit`'s pruning by `max` compares a node's begin with the query's end.

Run: `go test ./integration -run TestQ2Shape -v` in `tests/`, `go test ./adt -run TestQ2 -v` in `pkg/`.
Discussion: `notes/specs-only/ledger.md`, the 2026-11-27 entry "Q2 widening stopped".
