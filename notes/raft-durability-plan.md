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
- **No separate handoff machinery.** What crosses a crash is named per node and kept in the
  client's per-node invariant: the file and raft's `nodeStable`. Everything else is per
  incarnation. A restart re-points `nodeStable` once the old incarnation has halted (§3.2).
- **One raft spec for clients with and without durability** (§4, designed with the spec skill
  and reviewed twice). The `Ready` contract is the main change:
  - its messages are sendable after the batch's write (`readyMsgs` + `stableRcpt`), or at
    once at a leader;
  - the write itself is a ghost update the client fires on the node's durable state
    (`nodeStable_persist`): when the write is durable, or at once if nothing is durable;
  - `Advance` takes the receipt;
  - `RestartNode` and `StartNode` start from any restart point;
  - `node.Stop` gives `halted`.

  Raft's promises are minted at the write, not at `Step` as today.
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

`D_i` is raft's durable state of node `i`, `nodeStable` (§4.1), at what the file decodes to.
Raft's internal invariant ensures that every promise other nodes hold is backed by it.

The invariant holds at every step because every durable change is one atomic step:

- `durableExt`'s `Write` replaces the whole file;
- in etcd, `walExt`'s `Save` appends records (§5.2).

So the invariant is opened around exactly that step. This is `crashfs`'s proof, scaled up.

Each `Write` must also re-establish `D_i` of the new contents. It does so by firing
`nodeStable_persist` inside the write's atomic update, and that is where raft's promises are
minted (§4.1).

### 3.2 Handing over from one generation to the next

Some per-node state must be exclusive to the running incarnation. For example: raft's
in-memory protocol state, the replica's mutex invariants, the right to move the node's durable
state. The crash frame cannot get these back from the dead threads. The design keeps them out
of what crosses a crash:

- **What crosses a crash.** It is all named per node and kept in the client's per-node
  invariant (§4.4):
  - the durable file;
  - raft's `nodeStable` (exclusive) and `restartable` (persistent);
  - a way to get `halted ι` for the incarnation that ran.
- **What is per incarnation.** Raft's volatile ghost state, the driver token, and a batch's
  obligation and receipt (`readyStable`, `stableRcpt`) are indexed by the incarnation `ι`.
  After a crash, they constrain nothing that runs.
- **Re-pointing.** `nodeStable` is re-pointed to the new incarnation by `nodeStable_bind`, a
  ghost update that needs `halted ι` of the old one. `halted ι` comes from one of two places:
  - `node.Stop`, for `durablekv`'s in-process restart;
  - the old generation's `crashed`, through `□ (crashed -∗ halted ι)`, which `RestartNode`
    and `StartNode` give, for a real crash.
- **Why a crash mid-restart is harmless.** Everything a restart takes is persistent, so the
  invariant holds however a crash interrupts the restart.

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

**One spec, for every client.** The node API (`Spec/.../Api.lean`, `InvNode.lean`) changes
so that one spec serves both:

- a client that makes nothing durable (`examples/kv`, `kvwitness`, etcd's server under a
  theorem with no crashes);
- a client that does (`examples/durablekv`, and etcd with its WAL).

The `Ready` contract is the main change. `Advance` gains one premise. `RestartNode` and
`StartNode` generalize from an empty storage to any restart point. `node.Stop` gets a spec in
the API. Everything else is unchanged:

- `node.Ready.spec`, `Step`, `Propose`, `ProposeConfChange`, `Tick`, `ReadIndex`,
  `TransferLeadership`, `ReportSnapshot`, `ReportUnreachable` and `ApplyConfChange`;
- `sentMsg`, `stepIn_intro`, and the `MemoryStorage` specs.

The design follows the spec skill's TaDa principle. Raft's specs take and give back ghost
state the client owns: the node's durable state, `nodeStable`. The client keeps whatever
invariant it wants over it:

- in its own frame, when nothing is durable;
- in an invariant with the file or the WAL, when something is.

The candidate went through two rounds of the `spec-reviewer` agent on 2026-10-28. The
defects found and repaired are in §4.6. It is a design: nothing is compiled, and the user
has not reviewed it yet.

### 4.1 Vocabulary

**Pure** (`NodeApiVocab.lean`):

- **`Stable := ⟨hs, snap, prev, ents⟩`** is what a restart reads back: the hard state, the
  latest snapshot (`Option SnapTrip`), the log's start `prev` (the snapshot's id or a
  compaction point above it), and the entries after it.
  - `Stable.init` is the empty one.
  - `Stable.Wf` says `prev ≤ snapshot ≤ commit ≤ last entry`, with the entries consecutive.
  - `Stable.commit` is `max(hs.Commit, prev.index)`.
- **`Delta := ⟨h, snap, es⟩`** is a `Ready`'s write (`doc.go`, step 1). `Stable.next P δ`:
  - sets the hard state, if not empty;
  - with a snapshot, replaces the snapshot, `prev` and every entry (as
    `MemoryStorage.ApplySnapshot` does);
  - drops the entries at or after `es`'s first index, then appends `es`.
- **`Stable.snapshot P k` and `Stable.compact P c`** are `CreateSnapshot` and `Compact`.
- **`StoresStable σ hs P`** (decidable): a `Storage` at `σ` whose `InitialState` is `hs`
  holds `P`.

**Sealed** (`InvNode.lean`):

| Predicate | Kind | Meaning |
|---|---|---|
| `Inc` | type | an incarnation: one run of `StartNode` or `RestartNode` |
| `nodeStable γ N id ι P` | exclusive, timeless, one per node for the cluster's lifetime | node `id` restarts from `P`; `ι` is the incarnation whose batches move it |
| `restartable γ N id P` | persistent | `P` is a restart point of `id` |
| `halted γ N ι` | persistent | no goroutine steps incarnation `ι` again |
| `nodeInc n ι` | persistent | the node object `n` is incarnation `ι` |
| `freshNode γ N id ι P` | exclusive | a new incarnation from `P`, not yet bound |
| `readyStable γ N id ι b δ` | exclusive | batch `b`'s write obligation |
| `stableRcpt γ N id ι b` | persistent | batch `b` was written |
| `readyMsgs γ N id ι b r sts` | persistent | batch `b`'s messages, handed out with the last reported role `r` |

**Laws.** Every ghost update has `↑N ⊆ E`, and a client's own invariants sit outside `N`.

    nodeStable_persist   : nodeStable id ι P ∗ readyStable id ι b δ ={E}=∗
                             nodeStable id ι (P.next δ) ∗ stableRcpt id ι b ∗ restartable id (P.next δ)
    readyMsgs_send       : readyMsgs id ι b r sts ∗ stableRcpt id ι b ⊢ [∗ st ∈ sts] sentMsg id st
    readyMsgs_leader     : readyMsgs id ι b StateLeader sts ⊢ [∗ st ∈ sts] sentMsg id st
    nodeStable_bind      : nodeStable id ι P ∗ halted ι ∗ freshNode id ι' P ={E}=∗ nodeStable id ι' P
    nodeStable_snapshot  : (k within P's committed entries) →
                           nodeStable id ι P ∗ snapshotCert k ={E}=∗ nodeStable id ι (P.snapshot k) ∗ restartable …
    nodeStable_compact   : (c within P) → nodeStable id ι P ={E}=∗ nodeStable id ι (P.compact c) ∗ restartable …
    nodeStable_committed : nodeStable id st.inc P ∗ nodeDriver n st ⊢
                             ⌜st.handling = none → st.delivered.length ≤ P.hs.Commit⌝
    nodeStable_restartable : nodeStable id ι P ⊢ nodeStable id ι P ∗ (restartable id P ∨ ⌜P = Stable.init⌝)
    restartable_wf       : restartable id P ⊢ ⌜P.Wf⌝
    restartable_snapshotCert : restartable id P ⊢ ⌜P.snap = some k⌝ -∗ snapshotCert k
    readyRest_volatile   : nodeStable id st.inc P ∗ readyRest … ={E}=∗
                             nodeStable id st.inc (P.next δ) ∗ stableRcpt id st.inc st.batch ∗ (today's readyRest)
    nodeStable_exclusive, nodeInc_agree (with nodeDriver's st.inc)

`nodeStable_persist` is where raft's promises take effect: a vote, an acknowledgement, a
candidate's own vote. The client does it when its write is durable. A client that keeps
nothing durable does it at once.

### 4.2 `Ready`

`readyRest`, which `isReadyChan_recvAu` and `node.wp_readyRecv` hand out, changes in two ways:

- **The messages lose their `sentMsg`.** They come as one `readyMsgs γ N id st.inc st.batch
  (roleAfter st rd) sts`. They are sendable after the batch's write (`readyMsgs_send`), or at
  once by a leader (`readyMsgs_leader`).
- **It adds the batch's obligation** `readyStable γ N id st.inc st.batch (readyDelta h es L)`.

`NodeDriverState` gains three fields:

- `inc : Inc` (fixed, like `storage`);
- `batch : Nat`, the `Ready`s received;
- `role : StateType`, the last reported role.

`roleAfter st rd` is the `SoftState`'s role, or `st.role` when the `SoftState` is nil (it is
nil unless the role changed). This is etcd's `islead`, kept across `Ready`s.

This is `Ready.Messages`' contract in synchronous mode (`node.go:98-101`), not
`doc.go:79-86`'s (the issue above). It covers requests too: a `MsgVote` carries the
candidate's promise of its own vote. If a candidate sent `MsgVote` before `(term, vote = self)`
was durable, it could win with the others' votes, crash, restart a term back, and vote for a
rival in the same term. Two leaders in one term.

### 4.3 `Advance`, `Stop`, restart, start, allocation

- **`node.Advance.spec`** (and `dynamicSpec`) adds `stableRcpt γ N id st.inc st.batch`, and its
  post increments `batch`. `Advance` steps `stepsOnAdvance`, which holds the node's own vote
  and its acknowledgement of its new entries (`rawnode.go:410-425`). That is why this premise
  is needed: main's `notes/raft-implementation-facts.md` says "the self-ack must not reach the
  state machine before the append is durable". `batch` moves only at `Advance`, and the next
  `Ready` comes only after `Advance`, so at most one obligation is outstanding.
- **`node.Stop.spec`** (new to the API): `{{ isNode n γ N id ∗ nodeInc n ι }} n.Stop()
  {{ halted γ N ι }}`. `Stop` returns after `run` exits (`node.go:331-341`).
  - Proof obligation: the other methods' specs (`Advance`'s `storFloor` included) stay true on
    a stopped node. `durablekv`'s old `run` calls `Advance` after `Stop`, and its `tick`
    goroutine calls `Tick`.
- **`RestartNode.spec`.** The empty-storage premises and `nodeRestartBoot` are replaced by:
  - `StoresStable σ hs P`;
  - `cv.Applied' = 0`, or `P.prev.index ≤ Applied ≤ P.commit` (as `appliedTo`, `log.go:333`,
    requires);
  - `restartable γ N id P`.

  The post gives:
  - `isNode n`, `nodeInc n ι`, `freshNode γ N id ι P`, and `□ (crashed -∗ halted γ N ι)`,
    with the current generation's crash token;
  - `isCommittedLogLb γ dl`, with `dl` as long as `Applied` (or as `P.prev.index`);
  - `nodeDriver n` at `initAt := ⟨stor, dl, P.hs, none, ι, 0, StateFollower⟩` (`newRaft` ends
    in `becomeFollower`).

  The node's configuration is `P`'s snapshot's, or the static voters when `P.snap = none`.
- **`StartNode.spec`** (a bootstrap log): unchanged, except that the post adds `nodeInc`,
  `freshNode γ N id ι Stable.init` and `□ (crashed -∗ halted ι)`, and the driver starts as a
  follower at batch 0.
- **Allocation.**
  - `cluster_alloc_static` (no bootstrap log: kv, `durablekv`) gives, per voter,
    `nodeStable γ N id ι₀ Stable.init ∗ halted γ N ι₀ ∗ restartable γ N id Stable.init`, in
    place of `nodeRestartBoot`.
  - `cluster_alloc` and `dynamicCluster_alloc` (a bootstrap log: etcd's server) give the same
    **without** `restartable`. The bootstrap entries are committed in the ghost state but
    reach storage only through the first `Ready` (`bootstrap.go:77`), so the empty state is
    not a restart point.
  - **Scope restriction:** a node of a bootstrapped cluster that crashes before its first
    write cannot restart. etcd restarts such a member from an empty WAL. Record this in
    `decisions.md` at D1, and in `issues/` if it turns out to matter for safety.

### 4.4 The two kinds of client

**No durability.**
- The loop's invariant holds `nodeStable γ N id st.inc P` beside `nodeDriver`, threaded from
  allocation through boot.
- At start: one `nodeStable_bind`, with `halted ι₀`.
- Per `Ready`: one `readyRest_volatile`, which gives today's `readyRest` and the receipt
  `Advance` takes.
- `crashed` in `RestartNode`'s post is well defined in a proof with no crashes:
  `notCrashed` is in every generation's state interpretation. So no second spec is needed.

**Durability (`durablekv`).** A per-node invariant, outside `N` and named per node, so that it
survives a crash:

    ∃ f ι P, durableOwn_id f ∗ ⌜decode f = (σ, hs) ∧ StoresStable σ hs P⌝ ∗ nodeStable γ N id ι P ∗
      restartable γ N id P ∗ (halted γ N ι ∨ □ (crashed_L -∗ halted γ N ι))

- `persist` fires `nodeStable_persist` inside the atomic `durable.Write`, with the thread's
  `readyStable`.
- The snapshot write uses `nodeStable_committed`, `nodeStable_snapshot` and
  `nodeStable_compact`.
- `Cluster.Restart`: `node.Stop` gives `halted`. `start()` then runs `RestartNode` (whose
  premise comes from `restartable_wf`), then `nodeStable_bind`.
- With real crashes (D4), the crash frame turns `crashed_L` into `halted ι` at boot.
- Nothing a restart takes is exclusive, so a crash in the middle of `start()` leaves the
  invariant intact.

**etcd with a WAL (D5).**
- `Save`'s atomic update fires `nodeStable_persist`.
- The leader sends first, by `readyMsgs_leader`.
- The snapshot branch writes in several steps (`SaveSnap`, `Save`, `Sync`), so its delta may
  have to split into a snapshot part that is itself a restart point, then the rest. Settle
  this with the WAL model.

### 4.5 What moves inside raft's proof

- **Promises are minted at the write, not at `Step`.** The minting lemmas
  (`ownRaftGhost_step_grantVote`, `_app_accept`, `_higherTerm`) split in two:
  - a `Step`-time half, which records the promise as pending in the incarnation's volatile
    ghost state;
  - a persist-time half (`nodeStable_persist`), which mints the global witnesses.

  The safety arguments (election safety, log matching, leader completeness, commit) are
  about minted witnesses and should not change.
- **Volatile ghost state is per incarnation, durable state per node.**
  - *Per incarnation:* the in-memory `PState` and the pending promises.
  - *Per node:* `nodeStable`'s authority, in raft's cluster invariant.
  - *Proposals* stay global and independent of persistence: the term-`t` leader's log
    (`isTermLog`, `leadPrefix`) and the commit witnesses. A leader that crashes in term `t`
    restarts as a follower that voted for itself in `t`, so it never leads `t` again.
  - **A fresh incarnation that is never bound is inert.** It never gets a `stableRcpt`, so it
    never advances and never becomes leader.
- **Obligations the laws rest on:**
  - `readyMsgs_leader` needs batch `b-1` durable (by `Advance`'s premise). It also needs
    every message of a batch that ends as leader in term `T` to have been generated in term
    `T`, after the term-`T` vote was durable. This is Q1. The review traced it and found no
    counterexample.
  - `nodeStable_persist` on a halted incarnation (a client that stopped the node still holds
    the batch's obligation) needs the cluster invariant to keep a halted incarnation's
    pending promises until the bind.
  - `halted` from `crashed` needs the internal invariant to refute an old generation's steps
    through its `notCrashed` (`CrashToken.lean`).
- **Restart is from a restart point.** The node-local invariants (`VoteHistOk`, `acksOk`,
  `logRecs`) hold of every `restartable P` with the minted promises.
  - `Stable.init` is one only without a bootstrap log.
  - The commit index can go back in etcd, where a commit-only `HardState` change is not
    fsynced (§1.4). So `Hboot`/`commit_mono` become per incarnation, and the read-index
    argument is checked per incarnation (Q3). `StoresStable` stays exact until D5.

### 4.6 How the review changed the candidate (2026-10-28)

First round, against candidate 1:
- **A stale read.** Candidate 1 bound a new incarnation without the old one halted. The old
  incarnation, still running as leader, could confirm a `ReadIndex` from its in-memory
  acknowledgements (`raft.go:2144-2155`) and serve a stale read. `halted` and `node.Stop`
  repair it.
- **Compaction got stuck.** Candidate 1 kept the batch's target as a whole `Stable` in the
  driver, so `durablekv` stuck at its first compaction. The write obligation became a delta,
  numbered per batch, and `Stable` gained `prev`.
- **The empty state as a restart point.** Candidate 1 made the empty state a restart point
  in a bootstrapped cluster, which is unsound: a restart from it could commit a different
  index 1. `cluster_alloc` now gives no `restartable`.
- **A panic.** Candidate 1's `Applied` premise allowed `appliedTo` to panic.
- **The leader law.** Candidate 1 read the `Ready`'s `SoftState`, which is nil after a
  role's first `Ready`. The law now reads `roleAfter`.
- **Smaller fixes:**
  - incarnations became abstract (a reset heap can reuse a `Loc`);
  - `Stable.next`'s snapshot case now drops every entry;
  - laws were added, and masks stated.

Second round, against candidate 2:
- **`durablekv` could not discharge two premises:**
  - the snapshot index's bound, which `nodeStable_committed` now gives;
  - `Applied` at restart, which `restartable_wf` now gives.
- **`Stop`'s caller could not name the incarnation.** `nodeInc` names it now.
- **`initAt` was undefined.** It is defined now.
- **The persist law's obligation** for a halted incarnation is now written down.

### 4.7 Storage

`durablekv`'s `Storage` wraps a `MemoryStorage` with `Encode` and `OpenStorage`. It needs:

- a `StorageModel` instance (as `MemstorageInstance.lean`);
- the round trip `OpenStorage(Encode s) = s`;
- a storage-contract law: after `ApplySnapshot`, `SetHardState` and `Append` of a `Ready`, a
  storage that stored `P` stores `P.next δ`.

`InitialState`, deliberately omitted from the `Storage` contract today, comes back for
restart (`newRaft` reads it).

## 5. The applications

### 5.1 `durablekv` (D3, D4)

- **`handle`:**
  1. `ApplySnapshot`, `SetHardState`, `Append`;
  2. `persist`, which fires `nodeStable_persist` in the atomic write; a batch with nothing to
     write fires it at `P.next δ = P`;
  3. send (`readyMsgs_send`);
  4. apply;
  5. `Advance`, with the receipt;
  6. every `snapEvery` entries, `CreateSnapshot`/`Compact` and a second `persist`, with
     `nodeStable_snapshot`/`_compact` (§4.4).
- **`start`:** `durable.Read`, `OpenStorage`, `RestartNode`, `nodeStable_bind`.
  - In D3, `Cluster.Restart`'s `crash()` stops the node first, which gives `halted`.
  - In D4, `start` is the boot program and `P i L'` is the invariant of §4.4.
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
  - a follower calls `Save`, whose atomic update fires `nodeStable_persist`, and then sends
    (`readyMsgs_send`);
  - a leader sends first (`readyMsgs_leader`), then calls `Save`;
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
| D1 | Settle the node API of §4 with the user (the spec skill: critiques become principles, the approved spec an example), then the internal design as a `decisions.md` entry: which `RaftNames` maps are per node and which per incarnation, the pending promises, `halted` from `Stop` and from `crashed`, and the scope restriction of §4.3. Review with `spec-reviewer`. | D0; the cleanup's final `Ready`/`Advance`/snapshot specs |
| D2 | Raft: the split minting lemmas, the §4 API (`readyRest`, `Advance`, `Stop`, `RestartNode`/`StartNode` from a restart point, allocation, the laws), proved. Port the clients (`kv`, `kvwitness`, etcd's `raftNode`) with `readyRest_volatile`. | the cleanup landed |
| D3 | `durablekv` with its in-process restart, plain WP: `StorageModel`, `persist`, `handle`, `start`, porcupine `Ok` with `Cluster.Restart`. | D2 |
| D4 | Real crashes: `ExtCrashInterp durableExt`, one node per replica, `goose_dist_crash_adequacy`; T-dkv. | D3; a network extension (§3.4) |
| D5 | etcd: `walExt`, `isRNWal` → atomic `Save` firing `nodeStable_persist`, the leader path, bootstrap, the snapshot branch's split delta (§4.4). | D2, Q1, Q2 |
| D6 | etcd: backend durability, replay above the consistent index, the snapshot path's crash cases. | D5 |

Track D2–D6 with a TCB collection each (`etc/tcb-collections/`), as for the other proofs.

## 7. Open questions (D0)

- **Q1: the leader law** (`readyMsgs_leader`, §4.5). Can a `Ready` handed out at a leader
  (role `StateLeader`, as last reported) carry a message whose promise is not durable? The
  spec review traced the code and found no counterexample. Two paths to test:
  - a vote granted, then a campaign and a win, within one batch: impossible, since `MsgVote`
    leaves only in an earlier, non-leader batch, which is written before it is sent, and the
    node's own vote is stepped only by `Advance`;
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
- **Q4: compaction as a durable change.** `nodeStable_snapshot` and `nodeStable_compact` (§4.1)
  state that a snapshotted or compacted durable state stays a restart point. Proving them
  needs `isAcked`'s backing to accept "entry `i` is covered by a certified snapshot of
  committed entries". That is a proof obligation for D2, no longer a design question.
- **Q5: what the cleanup changes.** The snapshot and reconfiguration specs being rewritten
  decide how `rd.Snapshot` and the conf state enter `Stable` and `restartable` (the static
  voters when there is no snapshot; otherwise the snapshot's conf state). Re-read §4 against
  them before D1.
