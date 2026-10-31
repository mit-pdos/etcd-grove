# Proving raft's durable node API, then kvdurable's adequacy: the invariant changes (2026-10-31)

**Target.** The node API approved by the user is candidate 11
(`/home/ubuntu/spec-scratch/raft-durability/candidate.md`; the `spec` skill's
`examples/raft-durable-node-api.md`). After that, kvdurable's adequacy.

**Status.** This plan, before any proof is written. Reviewed once (`plan-review-1.md` beside the
surveys). Its repairs R2-R9 are adopted below. R1 and R10 await the user.

## Review 1 and what it changed (2026-10-31)

- **Candidate 12 (2026-10-31).** Three deletions from the spec:
  - *check* (approved by the user): its two outputs are given at the receive. The proof handles
    currency internally, by I-2's one-node-per-id and the `nodeRunning` gate, plus R9's
    leader-outbox invariant.
  - `storFresh`/`storFresh_alloc`: raft names a fresh key at the attach, in the continuation of
    `restartStorage`.
  - the driver's `batch` field.

  So I-4's once-register is allocated by raft inside `newRaft`'s proof. And `raft_enter`'s order
  needs no client-visible counter.
- **R1, resolved by the user (2026-10-31).**
  - **The resolution.** `RestartNode`'s precondition is the abstract `raftState` alone.
    `RaftState` gains `commit` (as of the last entered batch). The sealed body holds that index's
    certificate at a term `≤ S.term` and its committed log. `StorageHolds` allows
    `σ.commit ≤ S.commit`, and the AU loses its committed-log conjunct.
  - No `commitAt` predicate.
  - A commit-only batch's *enter* changes only `S.commit`, so a durable client applies it at once.
  - The candidate file records the amendment. The original finding follows.
- **R1 (design error; an API change for the user).** Amendment 2's derivation is false. A
  restarted node's `commitIn … σ.commit S.term` needs a commit fact at a term `≤ S.term`. A
  committed-log lower bound does not give one: a node at term 5 may write commit 10, which only
  the leader of term 9 committed. Weakening `t ≤ tm` breaks `campDyn` and vote requests.
  **Proposed:**
  - the Ready's post gives a sealed, persistent `commitAt γ id c`: the cut's `commitIn` at its
    own term, and a `termLB`;
  - `RestartNode`'s AU takes `commitAt γ id σ.commit` in place of the committed-log fact.

  Every real client writes a commit it got from a Ready, so the change is cheap for them. One new
  predicate.
- **R2 (design error).** The volatile half cannot open a per-node invariant: `ownRaftGhost` has
  no `N` and no token. And besides `vote_excl`, these look up an authority:
  - `ownLogGhost_ack_agree`, `heartbeat_commit_le_last`, `ownLogGhost_ack_le` (with
    `not_doomed`/`hbAck`/`hbResp`);
  - `win`, in the dynamic mode.

  **Adopted:**
  - a permanent per-id invariant, `slotInv` at `raftN γ .@ "slot"`, holding the entered D
    authorities' slot shares, which `ownRaftGhost` names;
  - `nodeVacant` keeps only the exclusive pieces;
  - `step_app_accept`, `step_heartbeat`, `step_snap_fastfwd`, `step_snap_restore` become fupds
    (today `==∗`), and `heartbeat_commit_le_last` an fupd (today pure). Their code callers'
    proofs change: this is not "statements kept".
- **R3.** The leader's self-match at `win` (`LeaderMatchOk`, `plastIndex`) is a pending ack that
  `step_commit` reads through `matchedOk`. **Adopted:** `matchedOk` exempts the self entry when
  its term is below `s.term`. (survey-protocol §3E was wrong here.)
- **R4.** A durable `ackAgree` for every current-term ack cannot be produced by *enter* once the
  base passes the ack. **Adopted:** a restart lemma from Leader Completeness for the acks in
  `(σ.commit, cE]`, in place of a durable `ackAgree`.
- **R5.** At the code level the proof runs in the dynamic mode (`ownRaftGhostR`, 147 uses outside
  `Protocol/`), whose `dynEnv` holds a candidate's `isCampK`, which cannot exist while its
  campaign is pending. **Adopted:** drop that conjunct; `win` takes the campaign from the tally's
  `voteJust` and a `slotInv` lookup.
- **R6.** The leader-side authorities (`reWins`, `reTerms`, `reLcm`, `reRdq`) are in the volatile
  half while a node runs, and in `nodeVacant` otherwise. The per-key `isCampK` goes in the
  volatile body.
- **R7.** The outbox wands range over the queued batch and the pending list (a re-granted queued
  vote). The durable half keeps copies of the entered fragments. *Enter*'s driver carries the
  batch's fragments to `Advance` (`pselfAck`, the self vote).
- **R8.** `raft_restart` gives `ownDurGhost` back, because the AU returns `raftState` unchanged.
  `raft_stop` cannot consume the client's batch token, so a generation counter in the slot makes a
  stopped node's batch unenterable.
- **R9.** F3 is a conjunct of `ownRaftGhost`'s body, stated in stage I: "a non-self message in the
  outbox that depends on pending promises implies `role ≠ leader`, and at a candidate, a pending
  campaign at `s.term`". (plan-review-1.md §R9 has the argument.)
- **R10, dissolved (2026-10-31).** `ResultsDyn.lean` holds only the allocation lemmas, which the
  code-level allocation uses and I-1 restates. `RefinementDyn`'s step lemmas are machinery for the
  Go-code proofs, which do have Readys and *enter*. No model-only result is left without an
  *enter*, so there is nothing to keep or retire. The original finding follows.
- **R10 (for the user).** The dynamic protocol model (`RefinementDyn`/`ResultsDyn`,
  `raft_dyn_alloc`) has no *enter*. Under I-1, pending promises would accumulate in it forever.
  Either:
  - its step cuts and enters at once (kept, at a cost);
  - or its model-level results retire, per the user's rule that model theorems are scaffolding
    once the Go API specs reach them.
- **Notes adopted:** `gg` starts at the attach for `storDL`; the cut batch's durable state has the
  same full log as the in-memory one; `ownRaftGhost_intro`'s signature; masks (kvdurable's
  namespaces disjoint from `N`); and the code proofs the lists left out (plan-review-1.md,
  Notes).

**Inputs.** Five read-only surveys of the current proof, each with file:line references
throughout, in `/home/ubuntu/spec-scratch/raft-durability/`:
- `survey-protocol.md`: the protocol ghost state and where promises are minted;
- `survey-node.md`: the node table, the Ready path, Stop;
- `survey-storage.md`: the storage contract and MemoryStorage;
- `survey-start.md`: allocation, starting a node, `newRaft`;
- `survey-adequacy.md`: kvreconf's adequacy, `durableExt`, kvdurable's functions.

**The user's order of work:**
1. First all the invariant changes.
2. Once those look good, reprove each function once, in parallel. The invariants and every
   statement are fixed before any proof starts, so each function's proof is written once, against
   final statements.

## 0. Amendments to candidate 11 the surveys found

All four are small. None changes the shape the user approved, and all are within its constraints.

1. **The bootstrap bound is against the stored commit.** In `RestartNode`, the scope premise
   `γ.bootLen ≤ S.last` becomes `γ.bootLen ≤ σ.commit`. The invariant `Hboot` (commit ≥ the
   bootstrap log's length) needs the commit, not the log's end (survey-protocol §3D). kvdurable has
   `bootLen = 0`, and etcd restarts after its first write, whose commit covers the bootstrap
   entries.
2. **The commit index's term at a restart** (survey-protocol §3D, risk 1). The restarted volatile
   half needs `commitIn … σ.commit t` for some `t ≤ S.term`. Today a node always learns a commit
   at term `t` after moving to `t`.
   - **Plan:** derive it inside raft from what the AU already gives: the committed log of length
     `σ.commit` agreeing with `S`, plus `TermsLe` (every entry's term is at most `S.term`). This
     is the first thing stage I checks.
   - **Fallback:** a law `raftState`'s durable half records the entered commit's `commitIn`. This
     is internal to raft (the commit is not in `RaftState`), and the AU's `σ.commit ≤` that record
     becomes a premise of `StorageHolds`. That would be an API change, and goes to the user.
3. **No API change for the restarted node's term lower bound** (survey-start, gap 6c). The run
   loop's `termLB γ.bud S.term` is extracted inside `RestartNode`'s proof when its AU fires
   (`raftState`'s sealed body holds it).
4. **No new law for skipping the configuration changes up to `a`** (survey-adequacy). `Advance`'s
   `skippedIn γ st.delivered v.applied st.delivered.length` is over the empty range while
   `delivered < v.applied = a`. Raft's proof must show `Advance` and `ApplyConfChange` sound with
   `v.applied > delivered`. That is an obligation (I-9), not an API change.

## 1. The invariant changes

### I-1. The protocol ghost: entered promises in the authorities, pending ones in the node

(survey-protocol §4; files `Protocol/GhostState.lean`, `StepGhost.lean`, `Refinement.lean`,
`RefinementDyn.lean`, `Facts.lean`, new `Protocol/Enter.lean`)

- **Principle.** The per-id authorities (`reVotes`, `reAcks`, `reEvs`, `reCamp`, `reVlogs`) hold
  only *entered* promises. So `votesTbl`, `winTbl`, `committedJust`, Leader Completeness and every
  `isX` fragment keep their meaning. They, `Ghost.lean`, `LeaderCompleteness.lean`, `StepR*`,
  `StepC`, `Model`, `CfgOverlap`, `LeadWit`, `SnapCertDyn` and `DecMap` are unchanged.
- **`Prom`**: a promise made in memory, not yet entered, with the persistent justification
  captured at `Step`. There are three kinds:
  - `vote T c d Fv`;
  - `ack T i`;
  - `camp T F k`.

  With it come `promJust` (persistent), `promFrag` (what *enter* mints) and `virt E π` (the
  entered maps with the pending list applied in order).
- **The durable half, `ownDurGhost γ id S`**, becomes `raftState`'s sealed body. It holds:
  - shares of the D authorities at the entered maps `E`;
  - `VoteHistOk E.voted S` and the term bounds (`AcksTerm`, `Hcamps_ok`, the events' terms
    `≤ S.term`);
  - `vlogsOk`, `logRecs γ S.base S.ents` and the base's facts;
  - `histsOk` at a durable known-leader bound `kd` (`kl` is forgotten at a restart);
  - `ackAgree` for the current term's acks (survey-protocol §3D, `acksOk`);
  - `termLB S.term` (amendment 3).
- **The id's slot, `idSlot γ id`**, becomes `nodeVacant`'s body when no node runs. It holds:
  - the other shares of the D authorities;
  - `ghostVar reVirt[id] ½ (entered ⊕ cut)`;
  - the queue of cut batches, of length at most one (`Advance` needs *enter*'s driver);
  - the leader-side maps (`reWins`, `reTerms`, `reLcm`, `reRdq`), each key carrying its campaign's
    `isCampK`. That makes them safe to mint at `Step`: a win needs entered votes, so its term is
    at most `S.term`.

  While a node runs, the slot is in a per-node invariant under `↑N`.
- **The volatile half, `ownRaftGhost γ id s md`.** Its name and signature are unchanged. Its body:
  - today's body over the pure `virt V πc` in place of the D authorities;
  - the pending list `πc` with its `promJust`;
  - for its pending part, each fragment as `□ (promFrags πc -∗ isX)`;
  - the outbox as `□ (promFrags πc -∗ isMessage m)`.

  Exact-equality invariants (`VoteHistOk`'s `voted !! s.term = some s.vote`, `campOwn`, `ownEvs`'s
  exact history) hold over `virt`. `vote_excl` refutes a fragment against the slot's entered
  authority (risk 3: the mask `⊤ ∖ ↑raftRegN`).
- **New lemmas (`Protocol/Enter.lean`):**
  - `ownRaftGhost_cut`, at each Ready: it moves `πc` into the slot's queue as `(durOf s, πc)` and
    gives `pendBatch γ id S S' πc` with `PendOk` (the freshness *enter* needs).
  - `raft_enter`: `ownDurGhost γ id S ∗ slot ∗ pendBatch γ id S S' π ={E}=∗ ownDurGhost γ id S' ∗ promFrags γ id π`.
    It inserts with today's helpers (`vote_insert`, `acks_add`, `ownEvs_ack`/`_vote`, the
    `reCamp`/`reVlogs` inserts), then releases the batch's `isMessage`s through the outbox wands.
  - `raft_restart`: `ownDurGhost γ id S ∗ idSlot (empty queue) ∗ the AU's facts ⊢ ownRaftGhost γ id (restartP S σ A)`.
    `restartP` is a follower with `kl := kd`, an empty outbox and votes, base `σ.base` and commit
    `σ.commit`.
  - `raft_stop`: the node's volatile half and slot give back `idSlot` with the queue emptied.
    A cut batch not entered is dropped with its token: a stopped node's updates are dead.
  - `check_leader`: at role leader, the outbox's messages need no pending promise. This is F3,
    risk 4. Either each message carries a flag, or a lemma shows that a leader's outbox holds
    only leader-type and self-addressed messages, the latter stepped at `Advance`.
- **Restated:**
  - the definitions `ownLogGhost`, `ownRaftGhost` and `_intro`; `ownRaftGhost_outbox` and its two
    users;
  - `ownLogGhost_ack`/`_vote`/`_campaign`, which produce a `Prom`;
  - `vote_excl`; `step_campaign`'s `isCampK` output; `outbox_app`/`_snoc`; `ownRaftGhostR`'s
    candidate conjunct;
  - the allocation lemmas (`Facts.lean:1195-1578`), which give `ownDurGhost` at `RaftState.init`
    and an `idSlot`.
- **Reproved (statements kept):**
  - the 7 minting step lemmas (`grantVote`, `win`, `propose`, `app_accept`, `stale`,
    `snap_fastfwd`, `snap_restore`), which append to `πc`. `win` takes its campaign from the
    quorum's `voteJust` (risk 2);
  - about 35 other step lemmas and the `ownLogGhost_*` family, mechanically;
  - the accessors in `ReadIndex`, `CommitWit`, `Term0`, `Facts`, `StepGhostMode`.

### I-2. The node table keyed by the node object; `nodeVacant` as the id's slot

(survey-node §3; `InvApi.lean:106-123, 1662-1760`, `InvNodeChan.lean:1068`, `RestartNode.lean:704`,
`StartNode.lean:496`)

- The node table becomes one cluster-wide table, keyed by the node pointer `n`. The node's names
  are inserted in `RestartNode`'s raw proof while `n` is still owned whole, which proves `n`
  fresh.
- `nodeStoppedRaw` marks a node object, not an id, stopped. Sequential nodes of one id become
  possible.
- `nodeVacant γ id := idSlot γ id ∗ (the id's node-API slot)`. That slot replaces the per-id
  `joinSlotU`/`nodeBootU`.
- **The escrow for `Stop`.** `run` refills it before `close(n.done)` (`node.go:450`), and `Stop`
  takes it after. `stop`'s handshake answers with `nodeVacant`; today it answers `True`
  (`InvNodeChan.lean:1155`, `node__run.lean:1187`).

### I-3. The Ready: *enter* and *check* built at the receive; the driver behind *enter*

(survey-node §2, §5; `InvApi.lean:2053-2420`)

- `readyRecv_open` builds the two view shifts. *enter*'s closure holds the `nodeDriver`
  construction (`InvApi.lean:2239-2257, 2323-2337`), `api_msgs`, `api_readStates` and `raft_enter`.
  `api_committed_lb` and `snapGiven` stay in the receive's post.
- Raft's share of `raftState` lives in the per-node invariant (I-2), opened by *enter* under
  `nodeRunning q`. It cannot live in `nodeDriver`, because `Stop` takes no driver.
- `run` builds no further Ready before `Advance` (`node.go:354, 435-446`), so at most one batch is
  cut and not entered.

### I-4. The storage contract keyed by `K`; `storDL` sealed with a new meaning

(survey-storage §2-3; `InvApi.lean:1679-1722`, `InvNodeRule.lean:550-600`, `MemstorageApi.lean`)

- `storFresh K` is a `dghostVar` once-register; `storFresh_alloc` is `dghostVar_alloc`. The attach
  sets it to `storKeyNames K sn`, raft's storage names. `nodeDriver` records `st.key` and
  `storKeyNames`.
- `nodeAppliedLbU`/`snapGivenU` read `storKeyNames K`, no longer `nodeStorNames γ id`. Everything
  below (`isStorageP`, `ownStorage`, `raftBnd`, `raftDL`, `InvStorageLaws`/`Read`, `StorageModel`)
  is keyed by `StorNames` already, and does not change.
- `storDL γ K i` means "the committed terms up to `i` are certified under K's names". It is
  given:
  - at the attach, at `σ.commit`;
  - by `nodeDriver_storDL`;
  - by `snapGiven_storDL` (`snapGivenU` carries it, minted at a snapshot Ready).

  "Delivered to the node" would be false at the attach, which is why the meaning changes.

### I-5. The detached MemoryStorage

(survey-storage §5; `InvMemstorage.lean`, four `MemoryStorage__*.lean`)

- `memStorFresh ms γs c sv` owns outright the justification authority (`jc`, every justified
  point `≤ c`) and the snapshot's home, with no validity.
- The attach (generalized `memStorInvP_alloc`) takes
  `memStorLock ∗ memStorFresh c sv ∗ □(∀ k ≤ c, J.B k) ∗ (⌜idx = 0⌝ ∨ J.SV sv ∗ J.DL idx)` and
  allocates `memJustInv`. That is where `J` is chosen. The lock invariant does not change.
- `Snapshot`, `ApplySnapshot`, `Compact`, `CreateSnapshot` take a mode argument
  `o : Option (Nat × SnapshotM)`, with `match o` in the post (the device `Snapshot`'s `if b then
  memSnapNone` already uses). Three mode-generic wrappers keep each proof one proof.
- `NewMemoryStorage` and `InitialState` change arity only.
- `memStorFresh_compacted` becomes `⌜c' ≤ c⌝`.
- `Append`, `Entries`, `Term`, `FirstIndex`, `LastIndex`, `SetHardState`: unchanged.

### I-6. Starting from a non-empty durable state

(survey-start §2; `newLogWithSize`, `newRaft.lean`, `NewRawNode.lean`, `InvBoot.lean:60`)

- **`newLogWithSize`** answers `FirstIndex = σ.b+1` and `LastIndex = σ.last`.
- **`newRaft`:**
  - the `loadState` and `appliedTo` arms are restored from `9470f19f32^:Proof/go_etcd_io/raft/v3/newRaft.lean`;
  - `wp_Restore_voters` becomes the general `confchange.Restore.spec`, for a joint `ConfState`;
  - the post has `dtk = σ.commit`, and `ownRaftPhys` at the restored `PState`.
- **`ownRaftPhys`, `rawNodeFresh` and `rnInit`** are generalized beyond a plain voter set to a
  general `CCState`. This may be the largest physical piece.
- **`ga`/`gdd` start at the attach bounds** (applied `max σ.b A`, certified terms up to
  `σ.commit`). `DtOk`, `RNFl` and `SnpOk` are to be checked at a non-zero start.

### I-7. Allocation, StartNode, Stop

(survey-start §1, §2.5-2.6; `InvNodeRule.lean:145-224`, `InvApiDecAlloc`, `InvApiJoin`, `InvApiBoot`)

- **Allocation.** `cluster_alloc` (both branches) and `joinAuth_join` give
  `raftState γ id RaftState.init ∗ nodeVacant γ id`, built from `joinSlotU`'s pieces and I-1's
  `ownDurGhost`/`idSlot`.
- **Deleted:** `nodeFounder`, `nodeJoin`, `nodeJoin_founder_impl`.
- **`nodeBoot`** becomes persistent: the bootstrap ghost moves into `raftState`/`nodeVacant`. Its
  `Hboot` is checked in the volatile half that `StartNode` builds, since it holds of the commit,
  not of `S`.
- **`StartNode`** binds before the call, as `RestartNode` does. The five helpers duplicated with
  `RestartNode.lean` are merged.

### I-8. `NodeDriverState`'s new fields

- `NodeDriverState` gains `key`, `durable`, `batch` and `role`. The 19 files that construct it are
  updated (survey-start §4).
- `role` is updated from the Ready's `SoftState` in the receive (`roleAfter`).

### I-9. Obligations the new specs add

- `Advance`/`ApplyConfChange` with `nodeConfig ⟨a, m⟩` and `delivered < a` (amendment 4).
- `check_leader` (F3).
- §0's commit/term derivation.
- At most one node per id: committed-log facts stay ungated.

## 2. The clients

- **kvreconf** (about 12 files, survey-storage §4, survey-start §4):
  - `StartCluster`, `Cluster__startNew`, `KvrStorageApi` (`bootStorage` → `restartStorage` with a
    frame), `newReplica`, `RunInv` (`raftState`, the driver's new fields, `K` keys);
  - `Replica__run` (*enter* applied at once, from the frame's `raftState` and the run loop's
    `nodeRunning`), `Replica__stop` (drops `nodeVacant`);
  - the `storDL` unfolds (`Replica__request.lean:121`, `Replica__run.lean:384`) become laws.
- **kv** (about 8 files): `Alloc`, `StartCluster`, `KVStorageInstance`, `KV__run` (`storDL`
  unfolds at `:464`, `:563`), and the exported `kv_bootStorage` (`Results.lean:129-141`), a
  trusted statement that changes (to the user).
- **etcd's server** (about 20 files):
  - `NewServerAlloc(On)`, `examples/common/{Alloc3,Defs}`, `NodeStart.lean:222-440`,
    `bootstrappedRaft__newRaftNode`;
  - `InvRaftNode` (the driver record, `Stop`'s post, the keys), `SDSnapLemmas.lean:38`;
  - the exported `server_cluster_alloc_on` (a trusted statement, to the user).

  etcd uses only `StartNode`. Its WAL `Save` is *enter*, at once until a WAL model exists.
- **kvwitness / RaftWitness/**: unaffected. It has its own copy of raft.

## 3. kvdurable and its adequacy

(survey-adequacy)
- **The adequacy theorem.** It has kvreconf's shape (`kvreconf_porcupine_safe` ←
  `kvreconf_adequate_of` ← `init_adequate`, `goose_adequacy` over the extension list), with
  `durableExt` added. Crashes are in-process, so no crash semantics are needed.
- **New pieces (about 0.5k lines):**
  - an `init_adequate` variant that passes the extensions' start resources (the files) to the
    program;
  - `HasExt durableExt`;
  - `durableOwn` split per file (a ghost map behind an invariant);
  - specs for `durable.Read`/`Write`, and the `durable` package's `Base`/`Init`;
  - `etc/gen-link.py --kvdurable`, `gen-init`.

  One new hypothesis: no `dir/replica-<id>` exists at start.
- **The 107 Go functions** (survey-adequacy §4 maps each to kvreconf's proof file):
  - 76 have the same text as in kvreconf: proofs ported;
  - 14 changed: `run`, `request`, `snapshot`, `snapshotter`, `applyEntry`, `read`, `newReplica`,
    `StartCluster`, `startNew`, `config`, `Storage.InitialState`, `Run`, `Main`, `RandomConfig`;
  - 17 are new: the codec, `openStorage`/`encode`, `start`, `persist`, `crash`, `restart`,
    `Crash`, `readSeqs.next`, `itoa`/`fileOf`, `SetHardState`, `snapIndex`.

  Estimated 18-20k lines, 8-9k of them new or changed.
- **The per-replica invariants:**
  - one holds the file, `raftState`, and the stored snapshot's certificate;
  - `dmu`'s holds the pending *enter*s and the contents `M`, which agree with the state after them,
    plus `crashed`.

  Because `encode` writes the hard-state copy that every Ready updates, the stored commit is at
  least the snapshot's index (the configuration point `a ≤ σ.commit`).
- **Independent of raft, can start at once:** the codec's pure round trip, the `durableExt`
  pieces.

## 4. Stages

- **Stage I (sequential, one author): the invariants and all statements, compiled.**
  - I-1 to I-8's definitions, restated lemma statements, new lemma statements with `sorry`, and
    the new spec files (`RestartNode`, `StartNode`, `node.Stop`, `node.run`, the receive's laws,
    `Advance`, `NewRawNode`, `newRaft`, `newLogWithSize`, the 6 MemoryStorage specs, `InvNode`'s
    sealed predicates and laws).
  - The clients' statements: kvreconf, kv and etcd invariants, the kvdurable statements.
  - `lake build` passing with `sorry`; `etc/gen-interface.py` regenerated, so the API diff is
    reviewed then; `etc/tcb-report.py` shows only the new `sorry`s.
  - First check: amendment 2's derivation. If it fails, the fallback goes to the user before
    stage II.
- **Stage II (parallel): each proof written once, against stage I's statements.** The work is
  partitioned so no two workers edit one file:
  - (a) protocol: 7 minting step lemmas, about 35 mechanical step lemmas, the `ownLogGhost_*`
    family, the accessors;
  - (b) `Protocol/Enter.lean`'s 5 lemmas;
  - (c) the storage: `InvMemstorage`, the 4 MemoryStorage proofs, the keyed bounds;
  - (d) start: `newLogWithSize`, `newRaft`, `NewRawNode`, `rawNodeFresh`, `RestartNode`,
    `StartNode`, allocation;
  - (e) the node layer: `readyRecv`/*enter*/*check*, `Advance`, `Stop`, `run`'s exit, about 15
    mechanical node-method wrappers, the `RawNode` proofs that unfold `ownRaftGhost`;
  - (f) the clients: kvreconf, kv, etcd;
  - (g) kvdurable (107 functions), then its adequacy.

  Each partition is checked by `lake build` of its targets. A proof that fails against its
  statement goes back to stage I, as a statement fix, not a second proof attempt.
- **Order.** (a)-(e) are parallel to one another. (f) needs (e)'s statements only, which stage I
  fixes, so it runs alongside. (g)'s proofs of `run`/`start`/`restart` need raft's API, which is
  likewise fixed in stage I. The adequacy goes last.

## 5. Risks

1. Amendment 2 (the commit's term at a restart); its fallback is an API change.
2. `win`'s campaign taken from the quorum's votes, not from `campOwn`.
3. `vote_excl` through the slot invariant: masks.
4. F3 (`check_leader`), unproved today.
5. A joint `ConfState` in `ownRaftPhys`/`rnInit`: the largest physical generalization.
6. Size: raft's proof is 130k lines; stage II touches tens of thousands of them.
