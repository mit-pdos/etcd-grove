# Repair, second round: the crash-story pass (R-A8 N1, N2, N4; N3 list form; S1, S2, S4, S5)

2026-11-09. Scope: make the crash restart compose (`rereview-cleanup.md`, CRASH-STORY PASS). Inputs:
`R-A8-server-boot-transport.md`, `repair-server-boot.md` "Re-review", open questions 2.7, 2.8, C42,
C43, Perennial's `CrashAdequacy.lean`, `CrashToken.lean`, OsFs's `Crash*.lean`, the Go of the WAL,
the snapshotter, `bootstrap.go`, `raft.go`.

## Per finding

### N1: raft's, W0's and 2f's vocabulary across a crash; the vacancy

**Fixed.** Each predicate the restart needs either has a stated generation-independence law (`⊣⊢` at
`⟨hG.goose_globalGS, L'⟩`: checkable, and meaning "built from the global ghost state only") or a
crossing law that consumes the old generation's exclusive resource.

- **Raft** (`SpecPlan/Spec/go_etcd_io/raft/v3/Api.lean`, new subsection "Crashes and generations"):
  - `global.spec`: `committedLb`, `committedOps`, `confAt`, `confDecisions`, `confDecided`,
    `snapsMade`, `snapValid`, `readCtxs`, `readCtx`, `readState`, `msgSent`, `msgCredit`,
    `freshIds`, `bootLog` are the same at every local generation. Realization: `own`s of `GF`'s
    names, invariants at `γ.ns`, later credits: all in `GooseGlobalGS`.
  - `raftState_gen.spec` (new): `raftState γ id D ∗ crashed ⊢ |={⊤}=> raftState@L' γ id D ∗
    nodeVacant@L' γ id` (at rest). Realization: `raftState` holds, besides the durable ghost var,
    the client's half of a per-id generation record (the name of `hG`'s crash token); `nodeVacant`
    is the vacancy token of that generation (a ghost map keyed by `(id, generation)`, inserted
    once). The crossing opens raft's invariant, moves the record to `L'` and inserts `L'`'s vacancy;
    the old incarnation's node invariant is dead (its steps refuted by `crashed` against
    `notCrashed`).
  - `raftState_crash.spec` (restated): takes `crashed` in place of the old generation's
    `nodeVacant` (which nothing produced after a crash), gives `raftState`/`nodeVacant` at `L'`,
    and is stated over a transparent `Durable.crashOk D b D'`. That relation is round 3's two
    cases, **extended to snapshot batches**: nothing of the batch (`j = 0`, old record), or all of
    it with the batch's record at a commit at or above the snapshot's index (`D.next b` at that
    commit; for a batch with no snapshot this equals round 3's `D.crashed b |ents| hs`).
  - **Why not R-A8's `isNode n γ id ∗ crashed ⊢ |={⊤}=> nodeVacant γ id`:** both premises are
    persistent, so the law would give two vacancies, and `exclusive.spec` would then refute it. The
    vacancy has to come with an exclusive resource that the crossing consumes, and `raftState` is
    that resource.
- **W0** (`SpecPlan/Spec/go_etcd_io/etcd/api/v3/State.lean`, crash laws only, new subsection "Across a
  crash"):
  - `etcdState_gen`, `etcdLb_gen`, `urlsRight_gen`, `urlsReserve_gen`, `soleMember_gen` (`⊣⊢`).
  - `envUpd_gen` (`⊢`; it follows from `etcdState_gen`, and is stated so that no client unfolds
    the atomic update).
- **2e** (`ApiBoot.lean`):
  - `srvNet_gen` (`⊣⊢`).
  - `memberBoot_crash` and `memberJoin_crash` (`… ∗ crashed ⊢ |={⊤}=> …@L'`, realized by raft's
    crossing).
  - `dataDirFresh_crash` (threads `crashRest`).
- **2f** (`rafthttp/Api.lean`):
  - `raftProto_gen` (an equality of `Http.Proto` values). `raftProto` had **no heap binders**: it
    was declared with only `(ν : Net GF)`, so its realization, which names `msgSent` at the heap,
    could not be written. The binders are now explicit.
  - `peerAddr_gen` (`⊣⊢`), realized from net/http's `protoAt` (see the request below) and
    `raftProto_gen`.
- **`crashGone_intro`:** deleted, together with `crashGone` (see N4), so its docstring no longer
  needs to match anything.

### N2: `crashOutOfScope` was an unconstrained opaque

**Fixed.** `crashOutOfScope ds` is now transparent:

    ∃ R, Wal.walRecs (walDirOf ds) R ∗ ⌜¬ R.crashScopeOk⌝

`disk_crash` states it at `L'`.

`Wal.Recs.crashScopeOk` (new, `wal/Api.lean`, transparent) is `Recs.confAboveOk ∧ ∀ s ∈ R.snaps,
s.index ≤ R.hs.commit`. It is stated over the records a restart reads, so it is physical:
- the first clause is at most one conf-change entry above the commit;
- the second is no snapshot record above the commit, i.e. the window between a received
  snapshot's fsynced WAL record and its batch's state record.

The realization cannot pick this disjunct at will. It needs `walRecs` at `L'` at bad records, and
only the WAL's trusted crash laws give that. W0's environment premise becomes "every crash leaves
each member's WAL meeting `crashScopeOk`", which is a statement about the run through `walRecs`'s
trusted meaning.

Every other crash point is covered. A snapshot batch interrupted before its WAL record, or after
its state record, is in scope, by the extended `raftState_crash`.

The false header claim (`ApiBoot.lean` 152-153, "keeps R1's durable invariant that at most one
conf-change entry is above `wcommit`") is gone. The header now says `diskState` keeps **no** such
bound (S4 too).

**Margin:** an at-rest crash of a lagging follower whose WAL holds two conf changes above its
commit is also out of scope by this statement, although raft handles it (`raftState_gen` has no
premise). Telling the two apart would need the record order (whether the state record comes after
the entries) in `Wal.Recs`.

### N4: one crash law per disk, at every point

**Fixed, with one window narrowed and recorded.**

**The crash law.**
- `disk_crash` now takes `diskState γ ds k ∗ crashed ∗ crashRest Ps` with `|={⊤}=>`.
- It gives, at `L'`, either `diskState ∗ diskIdle` (kind `k`, or `.member id`), or `crashOutOfScope`.
- `crashGone`, `crashGone_intro`, `crashOutOfScope_persistent` and `diskIdle_crash` are deleted.

**The header's "Crashes" section is rewritten.** It states:
- the realization of `diskState` per kind, at every step. The backend is closed (`beFile`) from
  `bootstrap`'s start to the open and from `Close` on, and open (`beDurInv ∗ beSynced ∗ beHist`)
  in between; the WAL is at rest or in `walWriting`; raft's `readyEnter` is deposited while a batch
  is in flight;
- how each part crosses: the WAL's laws; raft's `raftState_gen`/`raftState_crash`; 4a's
  `beFile_crash`/`beCrash`; the snapshotter's laws;
- when the kind changes: at `wal.Create`'s rename, with the parent directory fsynced before
  `Create` returns.

**The files no longer move into the running server's invariant** (`srvBuilt`'s realization text).
They stay in `diskState` through `diskAcc`.

**Where the disk is described, and when.**
- `srvClosed`: the file is deposited once `Close` returns.
- `bootstrap.lean`: "Crashes inside `bootstrap`" (every durable change is made through `diskAcc`).
- `NewServer.lean`: the Round 2 paragraph.
- `OpenBackend.lean`, `OpenSnapshotBackend.lean`: notes.

**4a: the crash law for a closed file at rest.** `Durable.lean`'s `beFile_crash.spec`:

    beFile p o ∗ beRevs p os ∗ crashed ∗ crashRest Ps ⊢ |={⊤}=> ∃ o', ⌜o' = o ∨ o' ∈ os⌝ ∗
      beFile@L' p o' ∗ beNoRevert@L' p ∗ crashRest (p :: Ps)

Realization: 4c's `fileHolds` (every byte clean and durable, name durable) is kept as it is by
OsFs's crash relation (`crashRest_take`). The revert case is the same OsFs gap as `beCrash`'s. The
coordinator's `boltOpenOptions_init` edit is untouched.

**`ReqCrashRecover`'s "at any point": served, and narrowed.**
- The snippet now lists the points: inside `NewServer`/`bootstrap`, before `Start`, while serving,
  inside `HardStop`/`Cleanup`, after `Cleanup`.
- Its Assumes now also excludes **a crash inside the backend's open**. 4a's `New` takes `beFile`
  in its precondition and allocates `beDurInv` inside the call, so during `New` the file is in
  neither the caller's disk nor a crash invariant. This is recorded in `OpenBackend.lean`, and the
  fix is requested below.
- The snippet compiles and vets clean.

**Recorded gap (see New decisions, 1):** how the program's crash frame takes `diskState` out of an
invariant that the running server opens inside callees' atomic updates.

### N3 list form / S1

- **N3 list form: fixed.** 4a already has `beRevs p os`, the list form, with `beCrash` taking
  `o ∈ os`. Changes:
  - `Snap.revertSt` is now `abbrev revertSt p os := Backend.beRevs p os`. The transitional
    `False` for two or more entries is gone.
  - rafthttp's `saveOk` second update now takes `∃∃ os, snapSaving ∗ Backend.beRevs p os`. It was
    the one-file `beRev p rv`, under which the server could not hand over two pending renames.
  - `snapshotHandler__ServeHTTP`'s sketch is updated to match.

  Two installs before a directory sync are now provable.
- **S1: not done; recorded** (New decisions, 7). The atomicity of a joint rename (source and
  destination together) needs one crash law over both `beCrash`, which is 4a's and needs the open
  backend's history, and `snapDbs_crash`, which is the snapshotter's. The restriction this leaves
  is not unsound: in the model the restart may fail (`NewServer` errs) where Go succeeds, and
  `ReqCrashRecover` returns on that error.

### Second tier, done in passing

- **S2:** `diskOk`'s crash clause now names a torn tail with no all-zero sector (`storage/Api.lean`).
- **S4:** see N2.
- **S5:** the `bootstrapped{Server,Storage,Backend}.Close` docstrings now say `beClosable`. Not
  done: removing `storage/Api.lean`'s superseded `beOpen`/`beTx` declarations, which other groups'
  text still names.

## The realization of each new law, in a sentence

| law | realization |
|---|---|
| `Raft.global` | Built only from `own`s of `GF`'s names, invariants and later credits (`GooseGlobalGS`). |
| `Raft.raftState_gen`, `raftState_crash` | `raftState` carries a per-id generation record and `nodeVacant` is per generation. Given `crashed`, the crossing moves the record to `L'` and inserts `L'`'s vacancy once (for `raftState_crash`, at a `D'` that the batch's "nothing acknowledged" argument allows). |
| `Raft.Durable.crashOk` | Transparent (round 3's cases plus snapshot batches written not at all or wholly). |
| `EtcdModel.etcdState_gen`, `etcdLb_gen`, `urlsRight_gen`, `urlsReserve_gen`, `soleMember_gen` | Ghost-variable halves, history fragments, tokens and invariants at `etcdN`: global. |
| `EtcdModel.envUpd_gen` | `etcdState_gen` under the atomic update (its masks are the global invariants'). |
| `Wal.Recs.confAboveOk`, `crashScopeOk` | Transparent, over the records `ReadAll` returns. |
| `Backend.beFile_crash` | 4c's `fileHolds` is fully durable, so OsFs's crash relation keeps it; `none` stays absent or empty; the revert case is the OsFs rename gap. |
| `EtcdServer.srvNet_gen` | An `own` of the cluster's names. |
| `EtcdServer.disk_crash` | Opens the disk's parts and crosses each by its own law (WAL, raft, backend, snapshot directory, boot or join token), then mints `diskState`/`diskIdle` at `L'` (keyed by the generation, as raft's vacancy); takes the out-of-scope disjunct exactly when the WAL's `R'` fails `crashScopeOk`. |
| `EtcdServer.memberBoot_crash`, `memberJoin_crash` | Raft's `raftState_gen` on the reserved durable state and vacancy (for a join right, held in the URL set's entry with a generation record), `Raft.global` and `peerAddr_gen` for the rest. |
| `EtcdServer.dataDirFresh_crash` | The per-directory token's OS resources (no backend file) are kept as they are by `crashRest_take`; the WAL and snapshot directories are absent by the closed world. |
| `EtcdServer.crashOutOfScope` | Transparent. |
| `Rafthttp.raftProto_gen` | Its parts name only raft's global vocabulary, `ν`'s fields and global names. |
| `Rafthttp.peerAddr_gen` | net/http's `protoAt` crossing (requested) and `raftProto_gen`. |

Each crossing law is not vacuous: it consumes the old generation's exclusive resource or OsFs's
`crashRest` (one-shot per file), or it is an `⊣⊢` between distinct instances.

## Requests

### To backend-schema

1. **`New` should take the file through an update at bbolt's open.** For example, an atomic update
   `<{ beFile p o ∗ beRevs p os }>` committed at the open, with `beDurInv γ p` handed to the
   allocation step. Then a crash inside `New` finds the file either in the client's disk or in its
   crash invariant. This closes the one N4 window left (`OpenBackend.lean`, `ReqCrashRecover`'s
   Assumes). It needs the same of 4c's `Open` (to bbolt).
2. **Confirm that `beCrash` holds after `backend.Close` returns** and before the client trades
   `beHist` for the returned `beFile`. Its realization then needs `boltFile`'s fragment of the
   file's meta after `boltRelease`. Alternatively, let `Close` give the file through an update.
   `srvClosed`'s realization relies on this.
3. **`Durable.lean`'s header:** I added the `beFile_crash` bullet myself, since the crash laws are
   mine. Nothing else is needed.

### To grpc-v3rpc (net/http)

- `Http.protoAt_gen.spec : protoAt a P ⊣⊢ protoAt (hG := ⟨hG.goose_globalGS, L'⟩) a P`. The
  reservation of an address is the run's, not a generation's. `Rafthttp.peerAddr_gen`'s
  realization needs it.
- Optionally `addrFree_gen`, for an address kept free across a crash.

### To raft-core

- `Model.lean:320`, `Durable.crashed`'s docstring, still says "A batch with a snapshot is not
  covered (`raftState_crash.spec`)". It should say that it is covered when nothing or all of it is
  written (`Durable.crashOk`, `Api.lean`).

### To server-core

- `EtcdServer__applySnapshot.lean`'s "last relay" Changes line names `beNoRevert`/`beRevert path o`.
  It should now be the revert list (`Snap.revertSt` = `Backend.beRevs`, R-A8 N3). Text only.
- `raftNode__start.lean` step 6's text is still right (`disk_crash` resolves the deposited batch).

### To the coordinator

- **`soleMember_intro`** (appended to `ApiBoot.lean` by another agent) takes `urlsReserve γ 1`, but
  `cluster_alloc` does not give it, and `urls_reserve` does not spend it, yet. That request was
  addressed to server-boot and is not in this pass's brief; I left both laws alone.
- **The open questions:**
  - 2.7 and 2.8's "verify-round" lines name `crashGone`, `crashGone_intro` and `diskIdle_crash`,
    which are gone. The vacancy now comes from raft's crossing, and the scope is
    `Wal.Recs.crashScopeOk`.
  - C42's revert is now a list (`beRevs`).

## New decisions

1. **The crash frame's access to the disk is a Perennial gap.**
   - Perennial's crash frame is proved at boot and gets only invariants and its own closure. The
     program keeps `diskState` in an invariant. The running server opens it through `diskAcc`
     inside callees' atomic updates (the WAL's `Save`, `SaveDBFrom`, commits).
   - The frame must take `diskState` out of that invariant for `disk_crash`. An accessor fired
     inside a callee's atomic update cannot rule out that the frame already took it: that needs the
     generation's `notCrashed`, which only a step owns, through the state interpretation.
   - This is not new to this pass. Every crash law over client-owned durable state has the same
     problem (4a's `beCrash` with `beHist`, 4c's `boltCrash` with `boltState`, the WAL's and the
     snapshotter's crash laws).
   - Options: a crash-aware invariant in Perennial (opened at a thread's step, which refutes
     `crashed`, and handed whole to the crash frame); or durable callees whose atomic updates admit
     a `crashed` answer, which they refute at their own step.
   - The old raft durability plan's `halted` discipline (`notes/raft-durability-plan.md` §3-4)
     avoided extraction by keeping per-node names that do not change at a crash. That works only
     while every durable change is one atomic step of an extension.
   - Please decide whether this goes to `notes/perennial-changes.md`.
2. **The vacancy comes with `raftState`'s crossing**, not with a node crash law (see N1 for why
   the latter is false). Raft's realization gives `raftState` a per-id generation record.
3. **The crash scope is stated over the WAL's records** (`Wal.Recs.crashScopeOk`), and raft's
   `raftState_crash` now covers snapshot batches that are written not at all or wholly. The scope
   is therefore narrower than round 2's "no crash during a snapshot-carrying batch": it is only
   the window between the snapshot record and the state record. It is also conservative about a
   lagging follower at rest (N2's margin).
4. **Generation independence is a `⊣⊢` law** (`*_gen`: raft's `global`, W0's, `srvNet`, `peerAddr`,
   `raftProto`). It is not a pure "does not take `hG`" claim, because the opaques must take `hG`
   by the convention.
5. **One disk crash law.** `crashGone`, `crashGone_intro` and `diskIdle_crash` are deleted. Whether
   a server runs is the realization's business. Every durable resource is in `diskState` at every
   step, and the files no longer move into the running server's invariant.
6. **`ReqCrashRecover` is narrowed** by one window, inside `backend.New` (request to
   backend-schema, 1). It is otherwise served at every point.
7. **S1 (the rename's joint crash) is left open.** The model may fail a restart that Go completes
   (backend reverted and source gone). Fixing it needs a joint crash law across 4a and the
   snapshotter.
8. **`raftProto` now has explicit heap binders.** It had none, which made it unrealizable.

## Replacement text for `top.md` K6

> **K6 — the history is the committed log's**: snapshots, restores, restarts and membership changes
> continue the same `σ`; an answered step is durable on a quorum (no crash transition in the model).
> After a crash too, at any point of a member's life: the program keeps each member's
> `EtcdServer.diskState` in its crash invariant and its crash frame applies `EtcdServer.disk_crash`
> (2e's one crash law per disk, from the old generation's `crashed` and OsFs's `crashRest`, over R1's
> `Raft.raftState_gen`/`raftState_crash`, the WAL's, the snapshotter's and 4a's crash laws), and the
> cluster's resources serve every generation (`EtcdModel.etcdState_gen`, `etcdLb_gen`, `envUpd_gen`,
> `Raft.global`, `EtcdServer.srvNet_gen`, `Rafthttp.peerAddr_gen`). Its environment premise (the
> user's decision, open question 2.8): every crash leaves each member's WAL so that `Open` +
> `ReadAll` returns records meeting `Wal.Recs.crashScopeOk` (at most one conf-change entry above the
> stored commit, `issues/raft-commit-lost-with-entries-kept.md`; no snapshot record above it), the
> case `disk_crash`'s `crashOutOfScope` names. Two recorded gaps: a crash inside the backend's open
> (`backend.New` takes the file in its precondition), and how the crash frame takes `diskState` out
> of an invariant the running server opens inside callees' atomic updates (Perennial: a crash-aware
> invariant).

## Build

- Changed modules and their directories:
  - `etc/specs-build.sh --dir` over `rafthttp`, `snap`, `storage`, `storage/wal`, `api/v3`,
    `probing`: **OK (138 modules)**;
  - `--dir` over `etcdserver`, `raft/v3`, `storage/backend`: **OK (509 modules)**.
- Every importer of the changed vocabulary modules (`etc/importers.py --leaves` over raft `Api`,
  W0 `State`, rafthttp `Api`, `ApiBoot`, `Durable`, wal `Api`, snap `Api`; 1447 `Spec` leaves):
  **OK (1447 modules)**.
- Last edits (`storage/Api`, the three `bootstrapped*.Close`, `NewServer`, `bootstrap`,
  `OpenBackend`, `OpenSnapshotBackend`): **OK (8 modules)**.
- Snippets: `cd examples && go vet ./specreq/etcdserverboot/` clean, `gofmt -l` empty.
