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

- [goose-array-indexref-loads-its-operand.md](goose-array-indexref-loads-its-operand.md)
  — every array index in the translated raft code is stuck. Blocks
  `quorum.JointConfig.IDs`, and with it `campaign`'s peer enumeration.
