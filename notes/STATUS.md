# Status (Lean port)

**Last updated:** 2026-10-06

Porting `main`'s Rocq election proof (`new/proof/go_etcd_io/raft/election_proof/`,
412 files, ~16.5k lines) to Lean on top of Perennial's Lean port
(mit-pdos/perennial `lean`, pinned at 8c75a3dd4).

## Done

- Lake project depending on Perennial (`lakefile.toml`).

## Next

1. The shared definitions: `protocol.v` (the protocol model and its ghost state),
   `defs.v`, `inv_*.v`, `step_lemmas.v`.
2. The 98 specs (`spec_*.v`), then the proofs (`proof_*.v`), then
   `election.v` (the links and the results).

## Differences from `main` besides the language

- Names follow Perennial's Lean conventions (`raft.wp_Step`, `own_raft_phys` →
  `ownRaftPhys`, …); see Perennial's `etc/lean-rename/renames.tsv` for the
  framework's Rocq → Lean names.
- The framework changes `main` made to Perennial's Rocq framework
  (`new/golang/theory/*.v`) are ported to Perennial's Lean framework where a proof
  here needs them, not to this repository.
