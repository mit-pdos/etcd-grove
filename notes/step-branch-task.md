# Filling in `raft.Step`'s branch proofs

`Proof/raft__Step.lean`'s per-message branches are the modules
`EtcdGrove/Raft/ElectionProof/Proof/raft__Step/<M>.lean`, one per Rocq file of
`~/etcd-grove-rr/new/proof/go_etcd_io/raft/election_proof/proof_raft__Step_helpers/
proof_raft__Step_<M>.v` (read-only extraction of the Rocq at feb5c73d4). Statements
are fixed; each unfinished proof is a `sorry` on the line after `-- PORT: proof`.
Several agents work at once in the worktree `/home/ubuntu/etcd-grove-lean-spec`, each
on its own group of modules.

## The task

* For each `-- PORT: proof` in your modules, port the Rocq proof, delete the marker.
  Each module's header says which Rocq `Local Ltac`s it would use: write them as
  local Lean macros if that helps.
* Never change a statement, or any file outside your modules. A helper lemma goes in
  your module before its first use (`private theorem`). If a lemma is unprovable as
  stated, leave the sorry, add `-- PORT: blocked: <what is wrong>`, report it.
* Read first: `notes/proof-porting-task.md` (general rules and idioms),
  `Proof/raft__Step/Base.lean` (the `raft.Step.Postulates` structure, `stepPost`,
  `finish_branch`, …), `Proof/raft__Step/MsgHup.lean` and `MsgBeat.lean` (finished
  branches, the models to follow), and the proofs other agents already finished in
  `Proof/` (e.g. `stepCandidate.lean`, `raft__handleHeartbeat.lean`) for idioms.
* Lemmas of modules you import may still be `sorry`: use them by statement.
* Budget about an hour per lemma; if stuck, narrow the `sorry` to the remaining goal
  with a comment and move on.

## Checking

    export PATH=$HOME/.elan/bin:$PATH
    cd /home/ubuntu/etcd-grove-lean-spec
    lake env lean EtcdGrove/Raft/ElectionProof/Proof/raft__Step/<M>.lean

**Never run `lake build`**: the modules yours imports are being edited by other agents
and a build would recompile them half-edited. Every module's `.olean` is already built
with its final statement, so `lake env lean` sees the right statements.

## Housekeeping

Scratch only in `.scratch/step-<group>/`. No git commands that change state.

## Report

Per module: remaining sorries (what is left), `PORT: blocked`, helpers and macros
added.
