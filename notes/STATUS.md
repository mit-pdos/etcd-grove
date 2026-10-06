# Status (Lean port)

**Last updated:** 2026-10-06

Porting the Rocq election proof (`new/proof/go_etcd_io/raft/election_proof/`) of
branch `worktree-raft-replication` at `feb5c73d4` (582 files, ~38k lines; was `main`'s
412 files until 2026-10-06, and the files below were first ported from `main`) to Lean on top of Perennial's Lean port
(mit-pdos/perennial `lean`, pinned at 8c75a3dd4).

## Done (ported from `main`; to be brought up to `feb5c73d4`)

- Lake project depending on Perennial (`lakefile.toml`).
- `protocol.v`, `defs.v`, `step_lemmas.v`, `inv_*.v`: ported from `main`, no `sorry`.
- `Base.lean`: `isInitialized` at `feb5c73d4`.
- The 98 specs of `main`; five proofs (`big_NewInt`, `big_Int__Int64`, `rand_Int`,
  `lockedRand__Intn`, `voteRespMsgType`) and their lines in `Election.lean`.

## Next (moving to `feb5c73d4`)

1. `plog.v`, `protocol.v` (7.1k lines: the model, then the ghost state, the
   step lemmas, Leader Completeness, the refinement obligation, the proposal
   registry).
2. `defs.v`, `step_lemmas.v`, `inv_*.v` (incl. the new `inv_memstorage.v`,
   `memstorage_instance.v`), updated by the `main..feb5c73d4` diff.
3. The 142 specs (41 unchanged from `main`), then the 145 proofs, then
   `election.v`.

## Differences from the Rocq besides the language

- Names follow Perennial's Lean conventions (`raft.wp_Step`, `own_raft_phys` →
  `ownRaftPhys`, …); see Perennial's `etc/lean-rename/renames.tsv` for the
  framework's Rocq → Lean names.
- The framework changes `main` made to Perennial's Rocq framework
  (`new/golang/theory/*.v`) are ported to Perennial's Lean framework where a proof
  here needs them, not to this repository.
