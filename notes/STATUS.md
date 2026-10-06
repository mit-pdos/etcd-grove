# Status (Lean port)

**Last updated:** 2026-10-06

Porting `main`'s Rocq election proof (`new/proof/go_etcd_io/raft/election_proof/`,
412 files, ~16.5k lines) to Lean on top of Perennial's Lean port
(mit-pdos/perennial `lean`, pinned at 8c75a3dd4).

## Done

- Lake project depending on Perennial (`lakefile.toml`).
- `protocol.v`, `defs.v`, `step_lemmas.v`, `inv_big.v`, `inv_logger.v`,
  `inv_storage.v`, `inv_raftlog.v`, `inv_tracker.v`: ported, no `sorry`.
- Five spec/proof collections (`big_NewInt`, `big_Int__Int64`, `rand_Int`,
  `lockedRand__Intn`, `voteRespMsgType`) and their lines in `Election.lean`.

## Next

1. `inv_misc.v`, `inv_raft_phys.v` (every remaining spec is stated on
   `ownRaftPhys`).
2. The remaining 93 specs (`spec_*.v`), then the proofs (`proof_*.v`), then
   `election.v` (the links and the results).

## Differences from `main` besides the language

- Names follow Perennial's Lean conventions (`raft.wp_Step`, `own_raft_phys` →
  `ownRaftPhys`, …); see Perennial's `etc/lean-rename/renames.tsv` for the
  framework's Rocq → Lean names.
- The framework changes `main` made to Perennial's Rocq framework
  (`new/golang/theory/*.v`) are ported to Perennial's Lean framework where a proof
  here needs them, not to this repository.
