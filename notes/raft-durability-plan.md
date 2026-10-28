# Durability for raft: plan (2026-10-28)

This is a plan only. No proof work starts until the raft cleanup in progress (snapshots and
reconfiguration) lands. This plan names where the cleanup's specs will move. It does not
depend on how the cleanup does them.

The goal is to reason about crashes and recovery: a node loses everything but its durable
state and restarts from it. The plan settles three things:

- what the program logic must provide;
- which specs change, in raft and in its clients;
- in what order to do the work.

It ends with the open questions to settle before proving anything (§7).

## 0. Summary

- **No new program-logic primitive.** Perennial's Lean port has crash semantics without a crash
  WP (§1.1). A generation is proved with the standard WP. What survives a crash is ordinary
  Iris invariants, plus a crash frame that each generation proves at boot from the per-generation
  `crashed` token. That is enough for raft and for `examples/durablekv`, because every change to
  durable state is one atomic step of a durable-state extension (§3.1). Old Perennial's
  `own_crash`, NC tokens and crash borrows are either not needed or derivable here (§3.3).
- **One derived pattern is needed: a generation handoff.** Volatile ghost state is named per
  generation. Durable ghost state is named per node, in an invariant tied to the durable file.
  The crash frame owns the right to start the next generation (§3.2). The pattern is general
  enough to propose to Perennial once a proof has used it.
- **The central spec change is in raft.** A promise (a vote, an acknowledgement, a candidate's
  own vote) is minted when it becomes durable, not at `Step` time as today (§4.2):
  - the messages of a `Ready` become sendable on a receipt that the batch is durable;
  - `Advance` takes that receipt, because it steps the node's own vote and acknowledgement;
  - restart from a non-empty storage gets a spec that rebuilds the node's ghost state from
    its durable state (§4.3).
- **First target:** `examples/durablekv`, which is already written, tested and translated, but
  not proved. It persists its whole state through `durableExt` and restarts with
  `RestartNode`. Its first proof runs its in-process restart with plain WP (stage D3). Real
  crash semantics come after (D4). etcd's WAL, server loop and backend come last (D5, D6).
- **Found while planning:** raft's `doc.go` lets any node send its messages while the same
  batch's entries are being persisted, against `Ready.Messages`' own documentation. Read
  literally, a follower could then acknowledge an entry that a crash loses.
  `issues/nonissues/raft-doc-send-before-same-batch-persist.md`, parked as documentation.

## 1. What exists

### 1.1 Perennial (Lean): crashes without a crash WP

- `Perennial/GooseLang/CrashLang.lean`: a node has one boot program, with no separate
  recovery procedure. A crash kills every thread and replaces the local state by one related
  by `Crash`. The global state, which includes the network, is kept.
- `CrashToken.lean`: each generation has `notCrashed`, owned by the state interpretation. A
  crash turns it into the persistent `crashed`, and the two are exclusive.
- `CrashAdequacy.lean`, `goose_crash_adequacy`: the client picks the boot precondition
  `P L` over the generation's local ghost state `L`, and proves, for every generation:

      P L -∗ threadTok ={⊤}=∗ WP e {{ φ }} ∗
        ∀ L', crashed(L) -∗ extsCrashStart L L' -∗ ownGoState(L') ∅ ={⊤}=∗ P L'

  The second conjunct is the crash frame. It is proved **at boot**, before the program runs,
  so whatever the next generation needs must already sit outside the threads: in invariants,
  or in the frame's own closure.
- `DistAdequacy.lean`, `goose_dist_crash_adequacy`: the same for a list of nodes, each with its
  own generations, sharing the global ghost state, so invariants span nodes.
- `ExtCrashInterp`: how an extension's ghost state survives a crash. `Ext/Fs/Adequacy.lean`
  keeps the old ghost names (`crashStart hL hL' := ⌜hL' = hL⌝`), so the old generation's
  `f fs↦ c` still describe the files.
- The worked example, `Perennial/Proof/.../examples/crashfs/Results.lean`, uses an ordinary
  invariant over the file's points-to and proves crash safety with nothing else.

### 1.2 This repository

- `GooseLang/Ext/Durable/` (`durableExt`): whole-file `Read`/`Write`, atomic and durable;
  the files survive a crash unchanged. Its specs include logically atomic ones
  (`wp_DurableWrite_atomic`), so `durableOwn` can live in an invariant. There is **no
  `ExtCrashInterp` instance yet** (`notes/STATUS.md`).
- `examples/durablekv`: a replica keeps its hard state, log and latest snapshot in one file,
  rewritten whole before it sends the messages of a `Ready` (`kv.go`, `handle`). It restarts
  with `RestartNode` from the file, with `Applied` at the snapshot's index.
  - Crashes are simulated in-process (`Cluster.Restart`: a `crashed` flag stops `persist`).
  - It has Go crash tests.
  - It is translated (`Code/.../durablekv.lean`), but there is no proof.
- `examples/kv` and `examples/kvwitness` persist nothing (they have no `SetHardState`).
  Their adequacy theorems state "no crash or restart".

### 1.3 The raft proof: durability is absent, not assumed

From a survey of the proof on 2026-10-28:

- **Promises are minted at `Step` against the in-memory state.**
  - `ownRaftGhost_step_grantVote` (`Protocol/Refinement.lean`) mints the vote `isVote γ v term cand`.
  - `ownRaftGhost_step_app_accept` mints the acknowledgement `isAcked`.
  - `ownRaftGhost_step_higherTerm` and `pbecomeFollower` handle term changes.
  - `VoteHistOk voted s` (`GhostState.lean`) ties the vote authority to the volatile
    `s.vote`/`s.term`.
- `acceptReady` only moves the already-justified messages, `msgsAfterAppend` included, into
  `rd.Messages`.
- **The `Ready` spec says nothing of `HardState` and `MustSync`** (`RawNode__Ready.lean`'s
  header: "which only a durability argument would need").
- **The `Storage` contract** (`InvStorage.lean`, `StorageModel`) models contents only.
  "Stored" means appended to the `Storage` object: `StableOk`, the receipts
  `appendReceipt`/`advReceipt`.
- **Every startup spec requires an empty storage:** `StartNode`, `RestartNode` and
  `NewRawNode` all require `σ.ents = []`, `HsEmpty hs`, `Applied = 0`. `newRaft.spec` allows
  a non-empty storage, but it is purely physical (`s.gh = {}`): nothing relates the storage to
  the ghost state.
- **Commit monotonicity is used across the whole run.** `Hboot` and `Step.commit_mono` use it,
  and the static single-voter read-index argument relies on it
  (`notes/raft-readindex-spec.md`, item 11).

A crash after a vote and before it is durable leaves a frozen `isVote` for `(term, cand)`
while the restarted node has `vote = 0`. The node can then vote twice. This is the canonical
election-safety bug, and it is outside the proof today (main's `notes/journal.md`,
"No crash or persistence model, at all").

### 1.4 etcd's server

- `raftNode.start` is proved (`Proof/.../etcdserver/raftNode__start.lean`).
- The WAL (`serverstorage.Storage`) is a names-only trust boundary. Its contract
  (`isRNWal`, `InvRaftNode.lean`) for `Save`, `SaveSnap` and `Sync` returns `True`.
- The loop sends a leader's messages **before** `Save` (`raft.go:240-242`) and a follower's
  after it (`raft.go:297-324`). This is the leader optimization of the Raft thesis §10.2.1.
- `storage/wal` is translated types and names only.
- The WAL syncs only when `raft.MustSync` holds (`wal.go:1015`). A `HardState` change that
  moves only the commit index is not fsynced. etcd's bootstrap acknowledges that the backend's
  consistent index can then exceed the WAL's commit (`bootstrap.go:615-624`).
- etcd does not set `Config.Applied`. raft hands back entries from the snapshot's index, and
  the apply loop skips those at or below the consistent index.

## 2. The target statements

1. **T-raft (raft's API).** The specs a durable application relies on:
   - `Ready` hands out the batch's durability obligation;
   - its messages become valid once the batch is durable;
   - `Advance` needs the batch durable;
   - restart rebuilds a node, including its ghost state, from durable contents.

   As today, the client guarantees are the specs; there is no separate model theorem
   (`go-api-specs-are-the-boundary` in memory).
2. **T-dkv.** `examples/durablekv` is linearizable (the porcupine check answers `Ok`) in every
   execution in which replicas crash and restart any number of times.
   - D3 proves it with the example's in-process restart.
   - D4 proves it with real crash semantics: `goose_dist_crash_adequacy`, one node per
     replica, messages through a network extension.
3. **T-etcd** (later). The server keeps acknowledged writes and stays linearizable across
   member crashes and restarts. This needs:
   - a WAL model;
   - the leader's send-before-`Save`;
   - bootstrap from the WAL;
   - the backend's durability with replay above the consistent index;
   - the snapshot path, `SaveSnap` → `Save` → `Sync` → `ApplySnapshot` → `Release`.

## 3. The program logic

### 3.1 Why plain invariants are enough

Each generation proves its successor's precondition at boot (§1.1). So every resource the
next generation needs must be one of two things:

- (a) held by an invariant whose ghost names do not change at a crash, meaning per node, not
  per generation;
- (b) owned by the crash frame's closure.

A thread's resources die with it.

For durable state, this is the discipline a crash WP would have imposed. The crash condition
of a WPC must hold at every step. Here, an invariant must hold at every step:

    durInv i := ∃ fs, durableOwn_i fs ∗ D_i (decode fs)

`D_i` is the durable half of node `i`'s protocol ghost state: its durable authority and the
facts that the promises other nodes hold are backed by the file.

The invariant holds at every step because every durable change is one atomic step:

- `durableExt`'s `Write` replaces the whole file;
- in etcd, `walExt`'s `Save` appends records (§5.2).

So the invariant is opened around exactly that step. This is `crashfs`'s proof, scaled up.

Each `Write` must also re-establish `D_i` of the new contents. That is where raft's promises
are minted (§4.2). A write of a state whose promises are not yet minted is fine: `D_i` asks
only that what was minted be backed, not that everything durable be minted.

### 3.2 The generation handoff (derived, reusable)

Some per-node ghost state must be exclusive to the running generation, for example:

- the authority over raft's in-memory protocol state (`PState`);
- the right to write node `i`'s file;
- the replica's mutex invariants.

The crash frame cannot get these back from the dead threads. The pattern:

- **Per-generation naming.** Volatile ghost state is allocated per generation. Its invariants
  name generation `L`'s ghost names. After a crash they are still allocated, but nobody owns
  their fragments, and they constrain nothing that runs.
- **The current generation.** A per-node ghost variable records the current generation:
  `curGen_i γ`, half in `durInv i` and half in the crash frame's closure.
  - Anything that must say "the running node's in-memory state" (for example, the global
    protocol invariant's per-node `PState` authority) is stated under `curGen_i`.
  - At a crash, the frame (holding `crashed L` and its half of `curGen_i`) re-points
    `curGen_i` to `L'` and allocates `L'`'s volatile ghost state from the durable contents in
    `durInv i`.
- **Refuting a dead generation.** `crashed L` refutes any old-generation token still in an
  invariant (`notCrashed_crashed`). This is how a disjunct like "generation `L` is mid-write"
  is closed after `L` crashed. With `durableExt`'s atomic `Write`, no such disjunct should
  arise.

This is three lemmas around Perennial's existing pieces: allocation, handoff and refutation.
Write them in this repository first (`Proof/CrashPrelude.lean` or beside the durable
prelude). When a second user appears, propose them to Perennial as a general library, by
Perennial's own workflow (CLAUDE.md, "Changes to Perennial").

### 3.3 What old Perennial needed, and what replaces it

| Rocq Perennial | Here |
|---|---|
| `WPC e @ E {{ Φ }} {{ Φc }}` (a crash WP) | WP, plus the crash frame proved at boot; `Φc` becomes the invariants' durable halves |
| NC tokens, `own_crash` | `notCrashed`/`crashed` per generation (`CrashToken.lean`) |
| `crash_borrow P Pc` (holding `P` across non-atomic steps, `Pc` at a crash) | not needed while every durable change is atomic (`durableExt`, a trusted `walExt`) |
| `idempotence` / recovery WPC | the boot program is the recovery; its precondition is `P L'` |

A crash borrow would be needed in one case: a thread holds exclusive ownership of durable
resources across several durable writes, and the intermediate durable states do not satisfy
the crash invariant. That would arise if the WAL itself is ever verified over a byte- or
block-level file model rather than trusted.

Even then, a WAL's replay assigns a meaning to every prefix of its records, so the
intermediate states likely do satisfy an invariant over "what replay returns". If one does
not, the general fix is a Perennial change, designed apart, not a local primitive
(`perennial-changes-general-only`). Nothing in D1–D5 needs it.

### 3.4 What is missing, and where it goes

- **`ExtCrashInterp durableExt`.** The files are unchanged, so the ghost names are kept, as
  for `fsExt`. It also needs a closed-extensions adequacy theorem for the extensions
  `durablekv` runs with. This goes in this repository (`GooseLang/Ext/Durable/Adequacy.lean`).
- **A network for a distributed `durablekv` (D4).** Today's `Cluster` runs all the replicas in
  one process with an in-process `send`. A node-per-replica variant needs Perennial's network
  extension (`Ext/Net`; the `netfs` example already combines it with crash adequacy). If that
  extension lacks something, record it in `notes/perennial-changes.md` then.

## 4. Raft's spec changes (T-raft)

### 4.1 Durable and volatile state of a node

- **Durable state.** `DurState := (hs : HardStateM, snap : snapshot metadata and conf state,
  ents)` is what a restart reads back. Node `i`'s durable authority `durAuth_i d` lives in
  `durInv i` (§3.1).
- **Volatile state.** The existing `PState` stays as the in-memory state. It may be ahead of
  `d`, and it is named per generation (§3.2).
- **What each kind of ghost state becomes.**
  - *Promises* (`isVote`, `isAcked`, a candidate's own vote, term bounds that others rely
    on) are backed by `d`.
  - *Proposals* stay as they are, global and independent of persistence: the term-`t`
    leader's log (`isTermLog`, `leadPrefix`) and the commit witnesses. A leader that crashes
    in term `t` restarts as a follower in term `t`, having voted for itself. It can never lead
    term `t` again, so term `t`'s leader log is frozen, and no persistence is needed for it.

### 4.2 Minting at durability

**Today.** `Step` mints a promise into the global ghost state at once.

**Proposed.** `Step` records the promise as **pending** in the generation's volatile ghost
state. The pending promises are minted into the global ghost state when the batch carrying them
becomes durable. Concretely:

- **`Ready`'s postcondition** adds the batch's durable target `D(rd)`, which is the previous
  durable state with `rd.HardState`, `rd.Entries` and `rd.Snapshot` applied, together with a
  ghost update:

      persisted_i D(rd) ==∗ [∗ m ∈ rd.Messages] msgOk m

  This makes every message of the `Ready` conditional on the batch being durable. That is
  `Ready.Messages`' contract in synchronous mode (`node.go:98-101`), and it is stronger than
  `doc.go:79-86`, which is the issue above. The condition covers the requests too: a
  `MsgVote` carries the candidate's promise of its own vote. If a candidate sent `MsgVote`
  before `(term, vote = self)` was durable, it could win with the others' votes, crash,
  restart a term back, and vote for a rival in the same term. Two leaders in one term.
- **`persisted_i D`** is a persistent receipt that node `i`'s durable state has reached `D`.
  It is minted by the durable write's logically atomic update, which updates `durAuth_i`
  inside `durInv i` and turns the batch's pending promises into global ones.
  - In `durablekv`, that write is `persist`'s `durable.Write`.
  - In etcd, it is `Save`, or `Save` followed by `Sync`.
- **`Advance`'s precondition** adds `persisted_i D(rd)`. `Advance` steps `stepsOnAdvance`,
  which holds the node's own vote and its acknowledgement of its new entries (main's
  `notes/raft-implementation-facts.md`: "the self-ack must not reach the state machine
  before the append is durable").
- **The leader exemption** (needed for etcd only; D5). `Ready`'s postcondition also gives:

      rd.RaftState = Leader → ([∗ m ∈ rd.Messages] msgOk m)  (needing only earlier batches durable)

  This states that a leader's `Ready` carries no promise that is not already durable. It is
  believed true (open question Q1):
  - a node can only become leader after its campaign `Ready` was handed out and persisted,
    since `MsgVote` leaves only in a `Ready`;
  - a `Ready` handed out while it was still a candidate already flushed its earlier
    `msgsAfterAppend`;
  - a leader's own acknowledgement and vote go through `stepsOnAdvance`, not `rd.Messages`.

  This is the kind of statement this proof has found false before, so it is a lemma to prove,
  not to assume.

**Clients that persist nothing.** `examples/kv`, `kvwitness`, and etcd today under a
no-crash theorem allocate `durAuth_i` with no file behind it. They can then mint `persisted_i`
at will. That is sound because their adequacy theorems have no crash frame. The tie to real
durability is in the client's `durInv`, not in raft's specs, so raft's specs stay uniform.

**What moves in the proof.** The minting lemmas (`ownRaftGhost_step_grantVote`,
`_app_accept`, `_higherTerm`) split in two:

- a `Step`-time half that records the promise as pending and updates `PState`;
- a persist-time half that mints the global witnesses.

`VoteHistOk` and `acksOk` hold of the durable state for the minted promises, and of `PState`
for the pending ones.

The safety arguments (election safety, log matching, leader completeness, commit) are about
minted witnesses and should not change.

### 4.3 Restart from a non-empty storage

The new spec for `RestartNode` / `NewRawNode` / `newRaft` over a storage whose contents are
`d` takes `durAuth_i d` and the next generation's `curGen_i`. It gives `ownRaftGhost` for the
new generation at a `PState` built from `d`, with no pending promises.

The proof obligation is that a durable state is a valid restart point: the node-local
invariants (`VoteHistOk`, `acksOk`, `logRecs`) hold of `d` with the minted promises. This
holds for two reasons:

- in `durablekv`, `d` is a state the node was in, namely the state at the time of some
  `Ready`;
- a promise is minted only once `d` reflects it.

Two cases go beyond "a state the node was in":

- **The commit index can go back.** In etcd, a commit-only `HardState` change is not fsynced
  (§1.4), so the durable commit can be lower than one the node had. `Hboot`/`commit_mono` must
  become per generation, with the commit witnesses (global, monotone) separate from the node's
  `committed`. The read-index argument's use of monotonicity is then checked per generation
  (Q3).
- **`Config.Applied`** must be at most the durable commit (`log.go:333`, `appliedTo`
  panics). `durablekv` passes the snapshot's index, which is at most the commit. etcd passes
  nothing.

### 4.4 Storage

`durablekv`'s `Storage` wraps a `MemoryStorage` with `Encode` and `OpenStorage`. It needs:

- a `StorageModel` instance (as `MemstorageInstance.lean`);
- the round trip `OpenStorage(Encode s) = s` on the fields the model holds.

`InitialState`, deliberately omitted from the `Storage` contract today, comes back for
restart (`newRaft` reads it).

## 5. The applications

### 5.1 `durablekv` (D3, D4)

- **`persist`:** the logically atomic `durable.Write` inside `durInv i`. It mints
  `persisted_i D(rd)` and the batch's promises. The `crashed` flag of the in-process
  simulation is the D3 stand-in for `crashed L`: a crashed incarnation writes nothing more.
- **`handle`:**
  1. `ApplySnapshot`, `SetHardState`, `Append`;
  2. `persist`;
  3. send, using `persisted_i` and the `Ready` ghost update;
  4. apply;
  5. `Advance`, with `persisted_i`;
  6. snapshot and compaction, followed by a second `persist`. This changes `d` without new
     promises: compaction must keep `d` a valid restart point (Q4).
- **`start`:** `durable.Read`, `OpenStorage`, `RestartNode` (§4.3). In D4, `start` is the boot
  program, and `P i L'` is `durInv i` with `curGen_i`'s frame half.
- **The client's epoch.** `Cluster` keeps the client's epoch durably, so operations are
  unique across client restarts. That is part of linearizability across crashes: a retried
  operation takes effect once. Its invariant is in the replicated state, so it does not
  depend on durability.

### 5.2 etcd (D5, D6)

- **WAL model.** A trusted `walExt` (the `GooseLang/Ext/<Name>` pattern, with
  `TrustedCode/.../storage.lean` models for the `serverstorage.Storage` methods and for
  bootstrap's WAL reads).
  - Local state: the record sequence and its synced length.
  - `Save` appends entry records, then a state record, and syncs if `MustSync`.
  - A crash keeps a prefix of the records that includes every synced one.
  - Replay gives `(hs, ents, snap)`, an entry at index `i` dropping those at or above `i`.
    This is the model whose atomicity Q2 questions.
  - Verifying the real WAL over a file model is out of scope (§3.3).
- **`raftNode.start`:**
  - a follower calls `Save`, whose atomic update mints `persisted`, and then sends;
  - a leader sends first under the leader exemption, then calls `Save`;
  - the snapshot branch: `SaveSnap` → `Save` → `Sync` → `ApplySnapshot` → `Release`.
    `Release` deletes WAL segments and snapshots up to the snapshot only after the hard state
    is synced (the code's comment at `raft.go:265`). Its spec must make that order necessary.
- **Bootstrap** (`bootstrap.go`): WAL open and `ReadAll`, `MemoryStorage` filled from it, and
  `restartNode`.
- **Backend durability (D6).** bbolt commits in batches. After a crash the backend is at its
  last commit, with the consistent index in the same transaction. The server replays raft's
  committed entries above it. The invariant: the backend's state equals the log applied up to
  its consistent index, and that index is at most the index of an entry committed in the
  cluster, which need not be the node's durable commit. The snapshot receiver's `.snap.db`
  rename (`notes/snapshot-receiver-epochs.md`) gets a crash case.

## 6. Stages

| Stage | What | Needs |
|---|---|---|
| D0 | This plan. Settle Q1–Q5 by reading the code, with the reconfiguration model checker's crash mode, and with Go crash tests (gofail, `durablekv`'s tests). File what is found in `issues/`. | none; can start now |
| D1 | The ghost design on paper, as a `decisions.md` entry: which `RaftNames` maps become durable-backed, the pending-promise state, `durInv`/`curGen` and the handoff lemmas (§3.2), the new `Ready`/`Advance`/restart specs. Review with `spec-reviewer` before writing code. | D0; the cleanup's final `Ready`/`Advance` specs |
| D2 | Raft: the split minting lemmas, `Ready`/`Advance` with `persisted`, restart from a non-empty storage. Port the clients: `kv`, `kvwitness` and etcd's `raftNode` mint `persisted` for free. | the cleanup landed |
| D3 | `durablekv` with its in-process restart, plain WP: `StorageModel`, `persist`, `handle`, `start`, porcupine `Ok` with `Cluster.Restart`. | D2 |
| D4 | Real crashes: `ExtCrashInterp durableExt`, one node per replica, `goose_dist_crash_adequacy`; T-dkv. | D3; a network extension (§3.4) |
| D5 | etcd: `walExt`, `isRNWal` → atomic `Save` minting `persisted`, the leader exemption, bootstrap. | D2, Q1, Q2 |
| D6 | etcd: backend durability, replay above the consistent index, the snapshot path's crash cases. | D5 |

Track D2–D6 with a TCB collection each (`etc/tcb-collections/`), as for the other proofs.

## 7. Open questions (D0)

- **Q1: the leader exemption.** Can a `Ready` with `RaftState = Leader` carry a message whose
  promise is not durable? Two candidate paths:
  - a vote granted, then a campaign and a win, within one batch: argued impossible in §4.2;
  - leader transfer (`MsgTimeoutNow`), where a forced campaign still sends its `MsgVote`
    through a `Ready`.

  Check with a Go test that steps a `RawNode` through such sequences without taking `Ready`.
  If it fails, etcd's §10.2.1 path loses safety: an issue, and D5 changes.
- **Q2: is etcd's `Save` atomic across a crash?** There are two ways the durable state can
  hold entries without their `HardState.Commit`:
  - a commit-only `HardState` is never fsynced;
  - a crash mid-`Save` can keep the entry records without the state record, if the WAL's
    repair keeps such a prefix.

  `issues/nonissues/raft-commit-lost-with-entries-kept.md` was parked because "atomic
  persistence of entries and `HardState` is part of the storage contract". If etcd's WAL does
  not provide that atomicity, the scenario may be reachable in etcd. Check:
  - whether either path reaches its trace's step 2, where the node receives indices 1–3 with
    commit 2;
  - whether it matters that no acknowledgement was sent.

  If a path reaches it, move the file back to `issues/` with an etcd reproduction (gofail at
  `raftAfterSave`, or a crash between the WAL's records).
- **Q3: commit monotonicity per generation.** Which of the raft proof's uses of
  `commit_mono`/`Hboot` survive a restart from a lower durable commit, and does the read-index
  argument (`raft-readindex-spec.md`, item 11) need the leader not to have restarted since
  the read began? A restarted node is a follower until it wins a later term, which suggests
  it does not.
- **Q4: compaction as a durable change.** `durablekv` persists after `CreateSnapshot` and
  `Compact`. The durable state then has a snapshot in place of entries. Is a compacted durable
  state still a valid restart point for every minted acknowledgement? An acknowledgement of
  index `i` must remain backed when entry `i` is only in the snapshot. That needs
  `isAcked`'s backing to accept "covered by a snapshot of committed entries".
- **Q5: what the cleanup changes.** The snapshot and reconfiguration specs being rewritten
  decide where `rd.Snapshot`'s durable target and the conf state enter `DurState`. Re-read
  §4.1–4.3 against them before D1.
