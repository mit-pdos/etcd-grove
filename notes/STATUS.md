# Status (Lean port)

**Last updated:** 2026-10-07

Porting the Rocq election proof (`new/proof/go_etcd_io/raft/election_proof/`) of
branch `worktree-raft-replication` at `feb5c73d4` (582 files, ~38k lines; was `main`'s
412 files until 2026-10-06, and the files below were first ported from `main`) to Lean on top of Perennial's Lean port
(mit-pdos/perennial `lean`, pinned at 0fe904415, which adds etcd-grove's Goose array fix
and Go-model/theory additions to the Lean framework).

## Done (at `feb5c73d4`)

- Lake project depending on Perennial (`lakefile.toml`); `Base.lean`.
- `plog.v`, `protocol.v` (7.1k lines: `Protocol/{Model,Ghost,GhostState,StepGhost,
  LeaderCompleteness,Refinement,Facts}.lean`): **fully proved**. `#print axioms` of
  `ownRaftGhost_step`, `leader_completeness`, `state_machine_safety`,
  `ownRaftGhost_alloc`: only `propext`, `Classical.choice`, `Quot.sound`.
- `defs.v`, `step_lemmas.v`, `inv_*.v` (incl. `inv_memstorage.v`): no `sorry`.
- The 142 specs and the 142 proofs (`raft.Step`'s branches in `Proof/raft__Step/`,
  one module per Rocq helper file). Trust boundary as in the Rocq: the state/logger
  axioms and nine `axiom … .wp_proof` for code outside the scope.
- `memstorage_instance.v` (`MemstorageInstance.lean`) and `election.v` (the links:
  `Election.lean`, generated; the results: `Results.lean`, which `#print axioms` the
  three top-level results): no `sorry` of their own. `raft.wp_Step` and
  `RawNode.wp_Propose` still depend on `sorryAx`, through `Proof/raftLog__slice.lean`'s
  one `sorry` (Rocq's deliberate `admit`, "the log fits in memory").

## Next

- Push Perennial's `lean` (0fe904415) so the pin resolves from GitHub.
- Follow `worktree-raft-replication` past feb5c73d4.

## Differences from the Rocq besides the language

- Names follow Perennial's Lean conventions (`raft.wp_Step`, `own_raft_phys` →
  `ownRaftPhys`, …); see Perennial's `etc/lean-rename/renames.tsv` for the
  framework's Rocq → Lean names.
- The framework changes `main` made to Perennial's Rocq framework
  (`new/golang/theory/*.v`) are ported to Perennial's Lean framework where a proof
  here needs them, not to this repository.
