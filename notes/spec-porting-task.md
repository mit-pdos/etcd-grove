# Porting a batch of `spec_*.v` files (feb5c73d4)

Instructions for an agent porting a batch of the Raft proof's Rocq specs. Several
agents work in this worktree at once (`/home/ubuntu/etcd-grove-lean-spec`, branch
`lean-spec`), so touch only your own files.

## What to write

For each `<fn>` in your batch, `~/etcd-grove-rr/new/proof/go_etcd_io/raft/election_proof/
spec_<fn>.v` (read-only extraction of the Rocq at feb5c73d4) becomes
`EtcdGrove/Raft/Spec/<fn>.lean`.

* Read `notes/porting-guide.md` (translation tables; "Spec and proof files"), then
  the model specs `Spec/lockedRand__Intn.lean` and `Spec/voteRespMsgType.lean`.
* Many `Spec/<fn>.lean` already exist: they are ports of an **older** Rocq version
  (branch `main`). Use them for their translation choices, but the statement must be
  the feb5c73d4 one: `git -C ~/etcd-grove diff main feb5c73d4 -- new/proof/go_etcd_io/
  raft/election_proof/spec_<fn>.v` shows what changed in the Rocq. Even when the Rocq
  did not change, the predicates it uses may have (below), so re-check every file.
* What a spec is stated on lives in `Defs.lean`, `StepLemmas.lean`, `Inv*.lean`,
  `Plog.lean`, `Protocol/*.lean` (all already ported to feb5c73d4). Grep them for the
  Lean name of each Rocq name. Changes relative to the old files that matter here:
  - `NState`: `role : PRole` (`.follower | .candidate | .leader | .preCandidate`),
    `prvals : GMap w64 Progress`, new `prevote : Bool`; `LogState` has `snap`.
  - `ownTracker cfg tv t` with `t : Trk := ⟨votes, prs, peers⟩`; `ownProgress pr p`
    with `p : Progress`; `ownInflights l i` (record-indexed; the old 3-argument one is
    `ownInflightsRaw`); `visitClosure` takes `I : GSet w64 → GMap w64 Progress → IProp`.
  - `ownStorage st prev ents ss`; `isStorage st = isStorageWith (ownStorage st) st`.
  - `ownReadOnly ro r` with `r : ReadOnly`.
  - `ownRaftPhys cfg r id s`: same signature; outbox via `outboxRel`;
    `raft.wp_store_state` takes a `PRole`.
* One `abbrev <T>.<M>.spec : Prop` per Rocq spec, inside the standard section
  variables; names as in the guide (package prefix for other packages:
  `tracker.Progress.ResetState.spec`). Keep the Rocq comments (design documentation),
  translated to Lean names. Header `/- Port of election_proof/spec_<fn>.v (feb5c73d4). -/`
  plus `Lean notes:` for differences. Helper definitions of a spec file go in it.
* Imports follow the Rocq `Require Export`: `inv_raft_phys` → `InvRaftPhys`,
  `inv_memstorage` → `InvMemstorage`, `plog` → `Plog`, `step_lemmas` → `StepLemmas`,
  `inv_big` → `InvBig`, `defs` → `Defs`, `New.proof.bytes` → `Perennial.Proof.bytes`,
  `spec_X` → `EtcdGrove.Raft.Spec.X`.
* Never change any file outside your batch's `Spec/<fn>.lean`. Do not weaken or change
  a statement; if one cannot be expressed, write the closest faithful statement, explain
  it in `Lean notes:`, and report it.

## Checking

    export PATH=$HOME/.elan/bin:$PATH
    cd /home/ubuntu/etcd-grove-lean-spec
    lake env lean EtcdGrove/Raft/Spec/<fn>.lean

The dependencies are built. If a spec of yours imports another spec of yours, build
that one first: `lake build EtcdGrove.Raft.Spec.<other>` (only your own
spec modules; never `lake build` anything else). For two or three specs, check in a
scratch file that `#check @<T>.<M>.spec` shows the expected binders.

## Housekeeping

* Scratch only in `/home/ubuntu/etcd-grove-lean-spec/.scratch/specs<N>/`.
* No git commands that change state. Read the Rocq from `~/etcd-grove-rr` or with
  `git -C ~/etcd-grove show/diff` (read-only).

## Report

Files written, compile status, Lean spec names, deviations from Rocq, and anything in
the `Inv*`/`Defs` interface that looked wrong or missing.
