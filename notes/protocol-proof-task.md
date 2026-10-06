# Filling in the proofs of one `Protocol/<M>.lean` module

The ghost part of `protocol.v` (feb5c73d4) was ported as a skeleton: definitions in
full, lemma statements exact, each unfinished proof a `sorry` on the line after
`  -- PORT: proof`. Several agents fill in these proofs at once, one module each.

## The task

* Your module is `EtcdGrove/Raft/ElectionProof/Protocol/<M>.lean`. Its header names
  the lines of `~/etcd-grove-rr/new/proof/go_etcd_io/raft/election_proof/protocol.v`
  it ports (read-only extraction of the Rocq at feb5c73d4). For each
  `-- PORT: proof` in your module, port the Rocq proof of that lemma and delete the
  marker.
* Never change a statement, a definition, or anything in another file. If a lemma is
  unprovable as stated (a mistranslated statement or definition), stop on it, leave
  the `sorry` and its marker, add a comment `-- PORT: blocked: <what is wrong>`, and
  report it. If you need a helper lemma, add it to your module just before its first
  use (`private theorem` unless it is generally useful).
* Ltacs of the Rocq file that the skeleton kept as comments (`log_mono_tac`,
  `destruct_ghost`, `role_ok_tac`, …) can become Lean macros in your module, if your
  proofs use them.
* Budget about an hour of effort per lemma. If a proof is stuck, narrow the `sorry`
  to the precise remaining subgoal, comment what is left, and move on.

## Context

* `notes/porting-guide.md` (tactics table), `Protocol/Model.lean`, and the modules
  your module imports. Iris proof mode: iris-lean (`.lake/packages/iris`), Perennial's
  ghost libraries `.lake/packages/perennial/Perennial/Ghost/*.lean`, and
  `.lake/packages/perennial/docs/PERENNIAL_PROOF_REFERENCE.md`. Pure goals: `omega`,
  `word`, `simp`, `decide`, `grind` if available.
* Lemmas used from earlier modules may themselves still be `sorry` in the skeleton:
  use them anyway, by their statements.

## Checking

    export PATH=$HOME/.elan/bin:$PATH
    cd /home/ubuntu/etcd-grove-lean
    lake env lean EtcdGrove/Raft/ElectionProof/Protocol/<M>.lean

**Never run `lake build`**: the other agents are editing the modules yours imports,
and a build would recompile them half-edited. `lake env lean` uses the imports'
already-built `.olean`s, which have the right statements.

## Housekeeping

* Scratch only in `/home/ubuntu/etcd-grove-lean/.scratch/<M>/`.
* No git commands that change state. Write only your module and your scratch
  directory (read anything).

## Report

Remaining `sorry`s (lemma, what is left), any `PORT: blocked`, helper lemmas added,
macros added.
