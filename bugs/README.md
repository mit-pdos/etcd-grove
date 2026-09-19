# bugs

Defects in the **tooling we depend on** — Goose, the `new/golang` model,
Perennial — that block etcd proofs. Not a place for bugs in etcd itself
(those are findings about the code under verification and belong in
[../notes/raft-implementation-facts.md](../notes/raft-implementation-facts.md)),
and not a place for proofs that are merely unfinished (those are `Admitted`
with a comment, and tracked in [../notes/STATUS.md](../notes/STATUS.md)).

The bar for a file here: **a proof cannot be completed, and no amount of
proof-writing skill would change that.** One file per defect, named
`<component>-<short-slug>.md`. Each one says what breaks, the evidence that
it breaks (file:line, and a probe that was actually run), what the fix is,
and what is blocked until it lands.

If a defect is fixed, delete the file — git remembers.

## Open

- [golang-len-of-nil-map-is-stuck.md](golang-len-of-nil-map-is-stuck.md)
  — `len` of a nil map has no rule, so it cannot step. Blocks
  `wp_ProgressTracker__TallyVotes`, whose joint config has `map.nil` as its
  second component.

## Fixed

- `goose-array-indexref-loads-its-operand.md` — every array index and array
  slice in the translated raft code was emitted against a *loaded array
  value*, which the model gives no step to, and `len`/`cap` of an array was
  emitted as a function value with no operand applied. Fixed 2026-09-17 in
  `goose/goose.go` plus new `go.len`/`go.cap` array rules in
  `new/golang/defn/array.v`; file deleted, see git history and the
  2026-09-17 entry in `../notes/journal.md`.
