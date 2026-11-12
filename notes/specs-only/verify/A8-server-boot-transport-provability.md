# A8: server boot, storage, transport (batches 2e, 2f): provability

Reviewer: independent provability round, 2026-11-09, at `1aa6fc1337` (worktree `specs-only`). Approach:
the `axiom` mindset on the trusted models (WAL, snapshotter, `net/http`'s `Serve`, addresses,
`diskOk`, the crash rule). I wrote the findings first. Only afterwards did I read
`open-questions.md`, `batch-2e.md`, `batch-2f.md` and `integration-I4.md`, to mark the findings
that are already recorded decisions.

## Verdicts

| batch | verdict | first-tier findings |
|---|---|---|
| 2e (boot, storage, WAL, snap, membership, v2stats, compactor, alarm, election/lock, config, features) | **FAIL** | F1-F7, F9 |
| 2f (rafthttp, and the `net/http` boundary it owns) | **FAIL** (narrow: the fix is mechanical) | F8, plus F3's `errorc` claim (`ReqErrorC`) |

Both verdicts are FAIL for findings that are not recorded decisions. The recorded decisions this
area also depends on: `crashScope` (open-questions 2.8/F8), the drain premise A7/F3, the closed world
5.4, the handler pool 5.5, and `v3client.New` (integration-I4, "Goose configuration").

## Counts

- **Function specs in the area:** about 235 (etcdserver boot/start/stop/member-op 41, membership 23,
  snap 8, v2stats 8, v3compactor 14, v3alarm 5, v3election 6, v3lock 3, rafthttp 103, storage 16,
  config 7, features 1).
  - **Checked against Go and their callees:** about 50. These are `NewServer`, `bootstrap`,
    `bootstrappedRaft.newRaftNode`, `Start`/`start`, `Stop`/`HardStop`, `Cleanup`, `GoAttach`,
    `RaftHandler`, `CutPeer`, `AddMember`, `StopNotify`, `storage.{Save,SaveSnap,Release,Sync,Close}`,
    `NewStorage`, `OpenBackend`, `OpenSnapshotBackend`, the hooks, `Snapshotter.{SaveDBFrom,
    DBFilePath,ReleaseSnapDBs}`, `RaftCluster.{ValidateConfigurationChange,AddMember,Recover}`,
    `NewMember`, the compactor's `New`/`newPeriodic` panics, `AlarmStore.{Activate,Recover}`, the
    five `electionServer` and two `lockServer` methods, and in rafthttp `Transport.{Start,Stop,
    AddPeer,Send,SendSnapshot,RemovePeer,Handler}`, `peer.{send,stop}`, `startPeer`,
    `pipeline.{post,handle}`, `snapshotSender.send`, `streamReader.{run,dial,decodeLoop}`,
    `streamWriter.run`, the three handlers' `ServeHTTP`, the two decoders, and `Http.{Serve,Listen,
    Listener.Close}`.
  - **Header and statement only (proof sketch read, Go not opened):** the remaining rafthttp
    internals (codec, picker, status, close notifier, stats), the other v3compactor and v2stats
    methods, config's getters, features. For these the verdict is **uncertain**, not PASS.
  - **Close as stated:** of the ~50 checked, 11 do not close (below). The rest close, modulo the
    vocabulary findings.
- **Snippets:** 25 checked (`etcdserverboot`: boot.go 8, storage.go 2, snap.go 1, members.go 1,
  compactor.go 1, lock.go 1; `rafthttp`: transport.go 6, receive.go 4 counting `Receiver`, snapshot.go
  2).
  - 16 are provable as stated.
  - 4 fail on the first-tier findings: `ReqCrashRecover` (F1, F2), `ReqLockOverInProc` (F6, and
    `v3client.New`, a recorded open item), `ReqErrorC` (F3), `ReqRestart`'s crash variant (F1).
  - 5 have assumption gaps (second tier): `ReqJoin`, `ReqStopAfterError`, `ReqInstallReceived`,
    `ReqStartThree`, `ReqPartition`.
  - The Go tests of trusted models (`ReqSaveOrder`, `ReqSnapRoundTrip`, `ReqMembers`) agree with
    the models (`Recs.save`/`saveSnap`/`release`/`entsAfter`, `saveAt`/`releaseBelow`, `ClusterSt`).
- **Laws:** all 35 of `ApiBoot.lean`, all of `wal/Api`, `storage/Api`, `snap/Api`, `membership/Api`,
  `v3compactor/Api` and `rafthttp/Api`'s 13, plus `Http`'s `reserve`/`handlerPool_alloc`/`reqTicket_*`.
  - **Not provable as stated:** `disk_crash`, `cluster_alloc` and `urls_reserve`.
  - **Vacuous or unusable:** `crashScope`, `crashGone` (no producer).

## What is good

- **The restart.** The durable-node shape is right and simple: `diskState` is client-owned and
  timeless, `diskIdle` is the volatile half, and `memberDisk := diskIdle (.member id)`. The restart
  after a stop is exactly `HardStop` → `memberStart_disk` → `NewServer`. `ReqRestart` closes:
  `diskCfgOk (.member _)` asks only `ForceNewCluster = false ∧ UnsafeNoFsync = false`, which
  `memberConfig` meets; the same `DataDir` gives the same `dirsOf`; and the post's `id = oid`.
- **The WAL model is the replay's.** The premise of `storage.Save` (no gap, nothing at or below the
  floor) is what `wal.go` needs. `Release` requires a *valid* saved record (the `walBaseLb` gap
  fixed). Commit-only saves leave `syncedCommit` unchanged, so they line up with raft's `wcommit`.
- **The snapshotter's model is true of `db.go`.** I checked `SaveDBFrom`'s keep-existing branch and
  `DBFilePath`'s `ReadDir` against the Go.
- **rafthttp's at-most-once argument is sound in design.**
  - Every pipeline and snapshot `POST` is `onceOnly`, so its ticket is withdrawn once.
  - Stream frames are deposited per (τ, index) against the reader's exclusive tokens. A replayed
    `GET` only creates deposits nobody withdraws. So `γ.dup = false` composes with `recvd`'s
    `msgCredit`.
  - `Process` takes `recvd ν m` and `srvNet γ.etcd ν`, and `srvNet`'s law in `ApiApply.lean:586`
    gives `ν.γ = γ.raft`. So the credit that reaches `raftNode.Step` is raft's `msgCredit γ.raft m`.
- **The compactor slot is correct against Go.** It requires periodic `|ret| ≥ 10ns`, which avoids
  `getRetryInterval() = 0`'s division at `periodic.go:177-189`. Negative retentions are fine.
- **Membership's `ccResult`** matches `cluster.go:306-391`, including the ordering (the removed
  check runs before the context's unmarshal panic).

## First-tier findings

### F1. Crash restart: `disk_crash` cannot be proved and cannot be used (2e, `ApiBoot.lean`)

The brief asks whether crash restart composes with raft's `RestartNode`/`raftState_crash` and the
backend's crash law. It does not compose, for four separate reasons.

1. **`crashScope` is a parameterless opaque `Prop`** (`ApiBoot.lean:522`).
   - **Why it fails.** The scope it is meant to state is a property of *the crashed state of `ds`*:
     `(st.durable.crashed b j hs).confAboveOk`, and `b.snap = none`. Those are exactly
     `raftState_crash`'s premises (`raft/v3/Api.lean:849-860`). A constant `Prop` cannot mention
     them, so the realization of `disk_crash` can extract nothing from it. Reading it as the
     universal "every crash state is `confAboveOk`" would make it false, and every result using it
     vacuous (PRINCIPLES, the `□∀` binder rule). No law introduces it, so `ReqCrashRecover` cannot
     establish it either.
   - **Already recorded?** The user's decision to accept the scope is recorded (2.8). Its
     formalization is not.
   - **Fix.** Make the scope a fact about the disk the client can see and the realization can use:
     - Either `disk_crash` concludes a disjunction: the disk restarts, or the crash state is outside
       the scope (`¬ confAboveOk` or a snapshot batch in flight), exposed as `crashOutOfScope γ ds`.
       The adequacy theorem then excludes that disjunct as its environment premise.
     - Or the deposited batch carries `⌜b.snap = none ∧ ∀ j hs, … → confAboveOk⌝` as a premise of
       the raft loop's deposit, which is false in general and so moves the scope to where it is
       decided.
2. **There is no WAL crash law** (`wal/Api.lean`).
   - **Why it fails.** `Recs.crashed` and `Recs.crashedMid` are defined (`wal/Api.lean:115-131`),
     but no law moves `walRecs wd R` to `walRecs wd R'` across a crash. Nothing records that a
     `Save` is in flight, which `crashedMid` needs. `disk_crash`'s realization (`walHolds R D`
     after the crash) therefore has no source. The header at `wal/Api.lean:49` and the
     `storage.Save`/`Sync` docstrings ("no crash in scope", `storage__Save.lean:11`,
     `storage__Sync.lean:6`) still describe round 1.
3. **`crashedMid` is false of the code under OsFs's crash model** (power loss: a dirty byte is
   "arbitrary", which includes its written value: `GooseLang/Ext/OsFs/Impl.lean:86-91`).
   - **The two cases.** `Save` writes the entries, then the state record, then fsyncs once.
     - A crash between the writes and the fsync can leave all the entries *and the new state
       record*. `crashedMid` (`wal/Api.lean:129-131`) admits only the old state. So `Save`'s
       update has to fire after the fsync, and the model then misses this crash state.
     - Firing at the write instead makes `Recs.crashed (R.save …)` claim the new commit is synced
       when it may be lost.
   - **Fix.** Add the disjunct `crashed ({R.save hs k es with syncedCommit := R.syncedCommit}) R'`.
     It matches `raftState_crash`'s `hs` with the batch's term and vote.
4. **The backend's crash law cannot be reached from `disk_crash`**, for two reasons.
   - **The resources are missing.** `Backend.beCrash` (`storage/backend/Durable.lean:86-94`) needs
     OsFs's `crashed ∗ crashRest … Ps`, threaded once through *all* files of the generation, and it
     gives `beFile` (4a's). `disk_crash` takes only `diskState ∗ crashGone`, per disk, at a single
     `hG`, with no next-generation heap. Neither `crashRest` (shared across disks) nor a generation
     appears. `Durable.lean`'s own note records the generation gap for 4a. `ApiBoot` has the same
     gap without a note.
   - **The predicates are different.** The server reads `Snap.beFile` (provisional) and
     `ServerStorage.beOpen` (provisional), not 4a's `Backend.beFile` and `beOpen γ q`. See F5.

- **Fix sketch.**
  - State `disk_crash` per generation, as `beCrash` is: `∀ L', … crashed ∗ crashRest(hG, L') Ps ⊢
    |={⊤}=> … @ L'`. Thread `crashRest` through a whole-program crash law that takes every
    `diskState`.
  - Add `walRecs_crash` and `snapDbs_crash` trusted laws over the in-flight write.
  - Name the producer of `crashGone` (W0 has none yet: open-questions 2.7 says "the crash rule's",
    but nothing states it). As stated, `crashGone` exists only for disks "whose server was running",
    so an idle disk at the crash loses its volatile `diskIdle` for good.
- **Callers affected:** `ReqCrashRecover`, `restart.go`'s `ReqCrashKeepsAnswered` (2d), W0's
  adequacy.

### F2. `diskAcc`'s masks block both the raft loop's write and the restart (2e, `ApiBoot.lean:261-263`)

`diskAcc γ ds := □ AU <{∃∃ k, diskState γ ds k}> @ ⊤ \ ↑diskN, ∅ <{…}>`. Opening it drops the
mask to `∅` while `diskState` is held. `diskState` holds `raftState γ.raft id D`, so two steps fail:

- **The raft loop's write.** Firing the deposited `readyEnter` inside `Save`'s update needs
  `↑γ.ns ⊆ E` (`raft/v3/Api.lean:436-441`). It cannot fire at `∅`, and `raftState` cannot leave
  `diskState`, because the crash needs it there.
- **`RestartNode`.** Its update is `@ ⊤ \ ↑γ.ns, ∅` (`RestartNode.lean:80`). Building it from
  `diskAcc` needs `⊤ \ ↑diskN ⊆ ⊤ \ ↑γ.ns`, that is `γ.ns ⊆ diskN`. That is the opposite of what
  the first step needs.

No choice of raft's namespace (`cluster_alloc`'s `N`) satisfies both. The header also calls
`diskN` "the program's disk invariants", yet the provider of an update `@ ⊤ \ ↑diskN` may not open
`diskN`.

- **Fix.** Make `diskAcc` an invariant-style accessor at `diskN`:
  `□ ∀ E, ⌜↑diskN ⊆ E⌝ → |={E, E ∖ ↑diskN}=> ∃ k, diskState k ∗ (∀ k', diskState k' ={E ∖ ↑diskN, E}=∗ True)`,
  with raft's `N` disjoint from `diskN`. Both steps then close.
- **Callers affected:** `raftNode.start` (2d, step 6), `bootstrappedRaft.newRaftNode`'s
  `RestartNode`, and every durable write.

### F3. A member that stops itself closes the backend under in-flight reads; the gate does not cover it (2e vocabulary, 2d `run`, 2c `Range`)

- **What the specs give.** `Start` gives `isServer` (persistent) and `srvGate s 1`. Each
  request-path call holds a share (`EtcdServer__Range.lean:89`). Only `HardStop`/`Stop` take the
  whole gate.
- **What the code does.** `run` also returns on `errorc` (`server.go:845-848`): a member that
  applied its own removal (`stopWithDelay`, `server.go:1366-1375`), or rafthttp's
  `reportCriticalError`. Its deferred shutdown then calls `Cleanup`. `Cleanup` takes `srvClosers`
  ("the backend's whole open token, which the store's readers rebuilt"), but the readers are out
  with the gate's shares.
- **So no proof of `run.spec` closes on the `errorc` arm.** Equivalently, `Range.spec`, `run.spec`
  and `Cleanup.spec` cannot all be true: this is exactly
  `issues/etcd-read-after-backend-close-panic.md`'s reproduction, a removed member serving
  serializable reads.
- **The snippets that claim otherwise.** `ReqErrorC` (`rafthttp/transport.go`: "logs it and stops,
  which is always safe") and `ReqRemovedSelfStops` claim the opposite. A7 and F3 of
  `open-questions.md` record the drain premise for `HardStop` only. 3.6 lists two other gaps; this
  path is not recorded.
- **Fix.** Either the fork's gate (F3's option), or a scope premise that names the self-stop. For
  example, `run`'s `errorc` arm is reachable only once no `srvGate` share is out. That is not
  establishable by any program that serves clients, so in practice the choice is the fork fix.
  Record it as a decision; it is not a doc fix.

### F4. Member ids that raft reserves (2e: `cluster_alloc`, `urls_reserve`/`AddMember`)

- **Raft's premises.** Raft's `cluster_alloc` and `freshIds_take` require
  `isLocalTarget id = false` and `id ≠ 0` (`raft/v3/Api.lean:570-590`).
- **What etcd's `ApiBoot` takes.** `cluster_alloc.spec` (`ApiBoot.lean:488-494`) has no premise on
  ids. Its realization note covers only duplicates and `0` ("`bootstrap` fails",
  `NewClusterFromURLsMap`, `cluster.go:84-91`).
- **The gap.** A SHA-1 id equal to `2^64-1` or `2^64-2` (raft's `LocalAppendThread` and
  `LocalApplyThread`) is accepted by `NewClusterFromURLsMap`. Then `memberBoot` has no raft
  resources to give, and the law is false at those inputs.
- **The same at runtime.** A `MemberAdd` whose `NewMember` id (time-salted) is `0` or a local
  target passes `ccResult`, which has no id check. `freshIds_take` then cannot run.
- **Fix.** A premise `∀ m ∈ ms, m.id ≠ 0 ∧ isLocalTarget (W64 m.id) = false` on `cluster_alloc`
  (the program computes the ids: `memberIdOf`). For adds, either a refusal disjunct in the model or
  a filed scope note (probability 2^-63). Not in `nonissues/`.

### F5. Provisional storage names never bridged to 4a (2e: `storage/Api.lean`, `snap/Api.lean`)

- **Two sets of names.** `OpenBackend`/`OpenSnapshotBackend` return `ServerStorage.beOpen be path
  img`, and the closers return `Snap.beFile`. Both are opaque and "provisional, batch 4a's"
  (`storage/Api.lean:76-90`, `snap/Api.lean`). 4a has `Backend.beFile`/`beOpen γ q`/`isBackend`
  (`backend/Api.lean:396,447`). No law relates them.
- **Steps that do not close:**
  - 2d's `applySnapshot` (its sketch hands the opened backend to `lessor.Recover`, `kv.Restore`
    and `cindex.SetBackend`, all over 4a's predicates);
  - `bootstrap`→`NewServer` (the realization of `bootOk` must give 4a's `isBackend` to `mvcc.New`
    and `NewLessor`; trusted here, so the gap is hidden inside an axiom);
  - the crash (F1.4).
- **`OpenSnapshotBackend` itself.** It is *translated* (`backend.go:61-70`). Its proof calls
  `os.Rename`, whose spec is over OsFs resources, but the statement is over the trusted ghost
  variables `snapDbs` and `Snap.beFile`, and no law relates `os.Rename` to them. Either make it
  trusted (names only) like its neighbours, or state the bridge laws (`snapDbs` file ↔ `osMeta`).
- **Fix.** Replace the provisional names by 4a's, or add the two bridge laws (`beOpen_backend`,
  `snapBeFile_backend`).

### F6. v3lock/v3election state their facts at the wrong prefix (2e)

- **What Go does.** `NewMutex(s, pfx)` and `NewElection(s, pfx)` work on `pfx + "/"`
  (`client/v3/concurrency/mutex.go:45-46`, `election.go:44-45`). 1d's specs say so (`NewMutex.lean:46`:
  `isMutex m s (pfx ++ "/")`).
- **What the server specs say.** `lockServer.Lock.spec` posts `lockedSince name k cr σ` and takes
  `mutexEff name` (`lockServer__Lock.lean:41,45`). `electionServer.Campaign.spec` posts
  `waitedFor name k cr σ` (`electionServer__Campaign.lean:54`). `Leader.spec` posts
  `firstCreate name …` (`electionServer__Leader.lean:45`).
- **Why that is false.** `noOlder name c` quantifies over every key with prefix `name` (`"lk"`
  covers `"lkz"`), which 1d's `lockedSince (name ++ "/")` does not give. A key `"lkz"` created
  earlier falsifies the stated post.
- **Fix.** `name ++ "/"` in all three posts (and in the effects' prefixes). `ReqLockOverInProc`'s
  check (the key starts with `"lk/"`) still follows.
- **Separately (recorded, integration-I4):** `v3client.New` has no spec, so `ReqLockOverInProc`
  and every election/lock caller cannot establish `isClient c γ none`.

### F7. `diskOk`'s stated meaning does not cover what the trusted specs rely on (2e)

`diskOk` is opaque and its docstring is its meaning (`storage/Api.lean:11-18`: WAL I/O, creating
the snapshot directory, opening bbolt). The trusted specs depend on more:

- **`SaveDBFrom`:** the directory fsync after the rename (`db.go:84-92`) returns an error with the
  file already renamed. The spec's error arm says "nothing changed" (`au` given back).
- **`ReleaseSnapDBs`:** `os.Open` and `Readdirnames` errors are returned (`snapshotter.go:46-53`),
  but the spec says `RET nil`. A logged `os.Remove` failure leaves a file the model says is gone.
- **`OpenSnapshotBackend`:** a rename failure after a successful `DBFilePath` cannot give the error
  arm's `Q none`.
- **`DBFilePath`:** its `ReadDir` failure.

**Fix.** List these in `diskOk`'s docstring, which is the adequacy theorem's premise, or give the
specs the true error arms. Axiom-mindset point: an opaque environment `Prop` is acceptable only if
its text names every failure it excludes.

### F8. rafthttp's message codec has no laws; the delivered message cannot be identified with the sent one (2f, `rafthttp/Api.lean:403-418`)

- **Where the gap is.** `pbEncodes`, `msgFrame`, `v2Frame` and `v2Compat` are `opaque … := True` or
  `[]`, with no laws.
  - **`decodeLoop`, `pipelineHandler`, `snapshotHandler`.** Each must conclude `recvd ν m` for the
    *decoded* `m`, from the deposit made for the *sent* `m`. That needs `pbEncodes` to be
    functional (`pbEncodes e m ∧ pbEncodes e m' → m = m'`) and `msgFrame` to be prefix-free ("frames
    self-delimiting").
  - **`messageDecoder.decodeLimit`'s post** gives only `pbEncodes e m`.
- **Why it matters.** Without this the at-most-once chain to `Process` and `Step` does not close.
  3h already provides `RaftPb.msgEncodes` with `Proto.encodes_fun` (`raftpb/Model.lean:410`). The
  provisional names were not replaced at integration.
- **Fix.**
  - Replace `pbEncodes` by `RaftPb.msgEncodes`.
  - Make `msgFrame` transparent (`be64 |e| ++ e`; the README: pure models are transparent).
  - State the msgappv2 codec's determinism as a law, or make `v2Frame` transparent.

### F9. `SaveDBFrom`, `snapDbs` and the crash (2e)

- **No generation for `snapDbs`.** `snapDbs` lives "for good in a per-directory invariant"
  (`ApiBoot.lean:94-101`). An ordinary invariant does not survive a crash. `memberDisk` keeps only
  the deletion right, and nothing re-establishes `snapDbs` (the files' certified images) in the
  next generation, although the restart's `RecoverSnapshotBackend` reads it.
- **Fix.** Part of F1's fix: a trusted `snapDbs_crash` law. `SaveDBFrom` fsyncs the file and the
  directory, so the model is true of a synced save.

## Second-tier findings

- **`Http.Serve`'s physical premise "at most `n` concurrent handlers"** (`net/http/Api.lean`,
  "Tickets"/handler pool) is not a property of `net/http`, which has no limit. A handler can
  outlive its client's request (the stream handler blocks until the writer closes; a snapshot
  handler continues after a client timeout), so the closed world does not bound it either.
  Recorded (5.5); the axiom's text should say it is a workload premise on the program's clients.
- **`NewMember.spec` reads `*now` without owning it** (`member.go:73`; trusted, a race in
  principle). It also never states that `memberIdOf` is invariant under URL permutation, though Go
  sorts (`member.go:64-65`).
- **`ReqJoin`'s assumptions omit** `isServer s1`, `srvGate s1 q` (for `AddMember`) and `s1`'s
  `srvRunning`. The panic's `id2 ≠ id1` needs `srvRunning_excl` or `srvBuilt_running_excl` against
  `s1`.
- **`ReqStopAfterError` omits `srvGate s 1`.** Moot under F3.
- **`ReqInstallReceived`** needs `ν.dbIn` kept by the `Receiver`'s lock invariant; `dbIn` is not
  persistent.
- **`ReqPartition`** is fine. `ReqStartThree`'s distinct ids follow from `srvBuilt_excl` and
  `srvRunning_excl`, but the snippet cites only `srvBuilt_excl`.
- **The `Cleanup`-before-`Start` path** (`srvBuilt_closers`) spends the start right. The disk's
  `diskIdle` is then lost and the directory can never be restarted (`embed`'s error path). Document
  it in the margin, or return `diskIdle` from `srvClosed` with the node's vacancy (the raft node
  started by `newRaftNode` keeps running: Go leaks it).
- **`imgBytes`** (`rafthttp/Api.lean:195`) is an opaque pure predicate. The same README point as
  F8.

## Ranking by need of revision

1. **`ApiBoot.lean`'s crash part** (F1, F2, F9), with `wal/Api.lean` (F1.2-3). The crash restart
   does not compose with R1 or 4a as stated.
2. **The stop protocol** (F3): `srvGate`/`srvClosers` against `run`'s self-stop. This is a
   soundness gap that the snippets claim is closed.
3. **`storage/` and `snap/` provisional names** (F5) and **`diskOk`'s text** (F7).
4. **`v3lock`/`v3election` prefixes** (F6): three one-line fixes.
5. **`rafthttp/Api.lean`'s codec** (F8): mechanical, using 3h's `msgEncodes`.
6. **`cluster_alloc`'s id premise** (F4).
7. Everything else, per the second-tier list.

## Already-recorded decisions this area relies on

- `crashScope`'s scope (open-questions 2.8/F8; only its formalization is F1.1).
- The drain premise for `HardStop` (A7/F3).
- The closed world (5.4) and the handler pool (5.5).
- `v3client.New` (integration-I4).

## Go bugs

No new Go bug was found. F3 is `issues/etcd-read-after-backend-close-panic.md` (already filed). F4
is a probability-2^-63 id collision with raft's reserved ids, not filed; it is a candidate for
`nonissues/` (etcd never checks for it, and raft relies on it).
