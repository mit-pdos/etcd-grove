# Porting a batch of `proof_*.v` files

Instructions for an agent porting a batch of the election proof's Rocq proofs. Several
agents work in this repository at once, so touch only your own files.

## What to write

For each `<fn>` in your batch, `~/etcd-grove/new/proof/go_etcd_io/raft/election_proof/
proof_<fn>.v` becomes `EtcdGrove/Raft/ElectionProof/Proof/<fn>.lean`.

* Read `notes/porting-guide.md` ("Spec and proof files" and "Tactics") and
  `notes/decisions.md` first, then the models `Proof/lockedRand__Intn.lean` (a proof
  with callee specs) and `Proof/big_NewInt.lean` (a trust-boundary axiom).
* The statement is fixed: `Spec/<fn>.lean` already states `<T>.<M>.spec`. The theorem
  is `theorem <T>.<M>.wp_proof (wp_C₁ : C₁.spec (GF := GF) (hG := hG)) … :
  <T>.<M>.spec (GF := GF) (hG := hG)`, one hypothesis per `Include` of
  `postulates_<fn>.v` in the same order. Each `Include FOO` names the callee whose
  `Spec/<callee>.lean` defines the spec; grep `Spec/` for the Lean spec name (specs of
  other packages carry the package prefix, `tracker.Progress.ResetState.spec`).
  Import your own `Spec` file and the callees' `Spec` files only.
* A Rocq `Axiom` in the proof functor (a trust-boundary triple) is a Lean `axiom … :
  <T>.<M>.spec (GF := GF) (hG := hG)` with the instance binders written out; check
  with `#check @…` that they are all there. Keep the Rocq comment explaining why it is
  trusted. A Rocq `Admitted` is a theorem whose unfinished part is a `sorry` with a
  comment.
* Keep the Rocq comments (translate names to Lean). File header
  `/- Port of election_proof/proof_<fn>.v. -/`, plus `Lean notes:` for differences.

## Doing the proofs

* Follow the Rocq proof's structure; it was written against the same specs and the same
  `ownRaftPhys` interface (`InvRaftPhys.lean`: `raft.wp_load_X`, `raft.wp_store_X`,
  `ownRaftPhys_tracker`, `ownRaftPhys_log_same`, …; `wp_raft_log` for logging calls).
  `ownRaftPhys` is sealed: use the interface, as the Rocq proofs do.
* Perennial's Lean proof mode: `.lake/packages/perennial/docs/PERENNIAL_PROOF_REFERENCE.md`,
  and worked proofs in `.lake/packages/perennial/Perennial/Proof/go_etcd_io/raft/
  v3_proof/*.lean`. Unsolved goals print their context: read them.
* Never change a statement in `Spec/`, `Inv*.lean`, `Defs.lean` or anywhere else outside
  your own `Proof/` files, and never weaken your theorem. If a proof needs a lemma that
  does not exist, prove it locally in your file (`private theorem`). If a spec or an
  interface lemma looks wrong or unusable, stop on that proof, leave a `sorry` with a
  comment, and report exactly what is wrong.
* Budget: do not spend more than about an hour of effort on any one proof. If a proof
  is stuck, leave the remaining goal as a `sorry` with a comment that says what is
  left, and move on. A partly done proof with a precise `sorry` is much better than
  none.

## Checking

    export PATH=$HOME/.elan/bin:$PATH
    cd /home/ubuntu/etcd-grove-lean
    lake env lean EtcdGrove/Raft/ElectionProof/Proof/<fn>.lean

The `Spec` modules are already built. Unused-section-variable warnings are harmless. Do
not run `lake build` on the whole project.

## Housekeeping

* Use only your own scratch directory,
  `/tmp/claude-1000/-home-ubuntu-perennial/c5cf1995-d725-409c-8019-529c34abc729/scratchpad/proofs<N>/`
  where `<N>` is your batch number. Never write in the scratchpad root or another
  agent's directory.
* Do not run git commands that change state, and do not edit `EtcdGrove.lean`,
  `Election.lean`, or any file outside your `Proof/<fn>.lean` files.
* Stay inside `/home/ubuntu/etcd-grove-lean` and your scratch directory; no operation
  needs anything else.

## Report

For each file: compiles or not, `sorry`s (where and what is missing), axioms, any local
helper lemmas that might be worth moving to a shared file, and any problem found in a
spec or interface lemma.
