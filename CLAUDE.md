# etcd-grove (Lean)

This branch verifies **etcd** — starting with its Raft implementation — in Lean,
using the Lean port of Perennial (branch `lean` of
[mit-pdos/perennial](https://github.com/mit-pdos/perennial)), which is a Lake
dependency (`lakefile.toml`, pinned in `lake-manifest.json`). The framework, the
Goose translation of etcd and etcd-raft (`Perennial.Code.go_etcd_io`,
`Perennial.GeneratedProof.go_etcd_io`) and the public etcd proofs live there; this
repository holds the etcd proofs that are not public.

It is a port of the Rocq development on branch `main` (`new/proof/go_etcd_io/raft/
election_proof/`). The Rocq notes on `main` (`notes/`) still describe the proof:
its design, the false statements found so far, what raft actually does. Read them
there (`git show main:notes/STATUS.md`); this branch's `notes/` only records what
is specific to the Lean port.

## Read the notes first

- `notes/STATUS.md` — where the port is.
- `notes/decisions.md` — how the Rocq structure maps to Lean, and why.

Before you finish, update `notes/STATUS.md` if anything moved.

## Layout

`EtcdGrove/Raft/ElectionProof/` mirrors `election_proof/`:

- the shared definitions (`Protocol`, `Defs`, `Inv*`, `StepLemmas`), outside the
  spec/proof discipline (predicates, pure lemmas);
- `Spec/<fn>.lean`: the one Hoare triple of a Go function, as `def <fn>.spec : Prop`;
- `Proof/<fn>.lean`: `theorem <fn>.wp_proof (callee specs …) : <fn>.spec`
  (an `axiom` at the trust boundary, `sorry` if unfinished); it imports only the
  `Spec` files of its callees;
- `Election.lean`: links every proof to its callees' proofs
  (`theorem <T>.wp_<M> : <fn>.spec`) and states the results; `#print axioms` on it is
  the trust base.

## Proof writing

Perennial's Lean docs (in the dependency, `.lake/packages/perennial/docs/`):
`PERENNIAL_PROOF_TUTORIAL.md`, `PERENNIAL_PROOF_REFERENCE.md`, `IRIS_PROOF_MODE.md`.

## Building

`lake build` (needs the `elan` toolchain in `lean-toolchain`).
