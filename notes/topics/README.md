# Topics

Durable technical notes, one file per topic: `kebab-slug.md`.

A topic note is for understanding that took real effort to build and that the
code does not state plainly — the shape of an invariant and why it has that
shape, how a chunk of etcd actually behaves, how a piece of tooling works in
practice. It should stay true across sessions; if it goes stale, rewrite it.

Not for: things the code says clearly, tactic documentation (see
`new/proof/PERENNIAL_PROOF_REFERENCE.md`), or one-off findings (those go in the
journal).

## Index

- [raft-proof-map.md](raft-proof-map.md) — what is in each Raft proof file and
  how they fit together.
- [goose-workflow.md](goose-workflow.md) — how Go source in the etcd forks
  becomes Rocq in `new/code/`, and how to change it.
