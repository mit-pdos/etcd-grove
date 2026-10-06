# Status (Lean port)

**Last updated:** 2026-10-06

Porting the Rocq election proof (`new/proof/go_etcd_io/raft/election_proof/`) of
branch `worktree-raft-replication` at `feb5c73d4` (582 files, ~38k lines; was `main`'s
412 files until 2026-10-06, and the files below were first ported from `main`) to Lean on top of Perennial's Lean port
(mit-pdos/perennial `lean`, pinned at 8c75a3dd4).

## Done (at `feb5c73d4`)

- Lake project depending on Perennial (`lakefile.toml`); `Base.lean`.
- `plog.v`, `protocol.v` (7.1k lines: `Protocol/{Model,Ghost,GhostState,StepGhost,
  LeaderCompleteness,Refinement,Facts}.lean`): **fully proved**. `#print axioms` of
  `ownRaftGhost_step`, `leader_completeness`, `state_machine_safety`,
  `ownRaftGhost_alloc`: only `propext`, `Classical.choice`, `Quot.sound`.
- `defs.v`, `step_lemmas.v`, `inv_*.v` (incl. `inv_memstorage.v`): no `sorry`.
- The 142 specs.

## Next

1. The 142 proofs (in progress, worktree `~/etcd-grove-lean-spec`, branch
   `lean-spec`).
2. `memstorage_instance.v`, `election.v` (the links and the results).

## Differences from the Rocq besides the language

- Names follow Perennial's Lean conventions (`raft.wp_Step`, `own_raft_phys` →
  `ownRaftPhys`, …); see Perennial's `etc/lean-rename/renames.tsv` for the
  framework's Rocq → Lean names.
- The framework changes `main` made to Perennial's Rocq framework
  (`new/golang/theory/*.v`) are ported to Perennial's Lean framework where a proof
  here needs them, not to this repository.
