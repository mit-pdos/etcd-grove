# Porting a batch of `proof_*.v` files

Instructions for an agent porting a batch of the Raft proof's Rocq proofs (at
feb5c73d4). Several agents work at once in the worktree
`/home/ubuntu/etcd-grove-lean-spec` (branch `lean-spec`), so touch only your own files.
`Protocol/Refinement.lean` there still has `sorry`s (another agent is proving it
elsewhere); use its lemmas by their statements.

## What to write

For each `<fn>` in your batch, `~/etcd-grove-rr/new/proof/go_etcd_io/raft/election_proof/
proof_<fn>.v` becomes `EtcdGrove/Raft/Proof/<fn>.lean`.

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
* A few `Proof/<fn>.lean` already exist: ports of an older Rocq version (branch
  `main`). Redo them against the feb5c73d4 Rocq and the current specs.
* `raft.Step.spec` and `RawNode.Propose.spec` are stated at `HeapGS HasLC.hasLC GF`
  (the ghost state holds an invariant); their proofs work at that instance too.
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
    cd /home/ubuntu/etcd-grove-lean-spec
    lake env lean EtcdGrove/Raft/Proof/<fn>.lean

The `Spec` modules are already built. Unused-section-variable warnings are harmless. Do
not run `lake build` on the whole project.

## Housekeeping

* Use only your own scratch directory,
  `/home/ubuntu/etcd-grove-lean-spec/.scratch/proofs<N>/` (gitignored)
  where `<N>` is your batch number. Never write in the scratchpad root or another
  agent's directory.
* Do not run git commands that change state, and do not edit `EtcdGrove.lean`,
  `Link.lean`, or any file outside your `Proof/<fn>.lean` files.
* Write only inside `/home/ubuntu/etcd-grove-lean-spec` (read the Rocq from `~/etcd-grove-rr`); no operation
  needs anything else.

## Report

For each file: compiles or not, `sorry`s (where and what is missing), axioms, any local
helper lemmas that might be worth moving to a shared file, and any problem found in a
spec or interface lemma.
