# Plan: restarting a member (`examples/etcd/restart`)

**Date:** 2026-11-02. **Status:** Scope decided: Q1-Q6 take the recommended options (the user,
2026-11-02). **R1 done** (2026-11-02): the Go program, its test and translation (below, "R1").
Follows the spec-first plan's steps (`notes/spec-first-plan.md`: Scope, Draft, Review, Test, Probe,
Freeze, Prove).

## Goal

A closed theorem about a cluster in which a member is **stopped and started again on its own data
directory**, so that the proofs cover what etcd does at a restart:

- replaying its WAL;
- loading its last snapshot and its backend;
- rejoining the cluster;
- being caught up, by entries or by a snapshot.

Every server result today starts each member once, on an empty data directory. The boot predicate
says so: `bootOk`'s `memStorFresh`, the empty hard state, raft started by `StartNode` with the members
as peers, and no remotes (the `Hnosnap` comment, `InvBoot.lean`). No member ever stops: `run` never
returns.

The example is separate from linkv3p, the user's choice (2026-11-02). That keeps the new premises
out of `linkv3p_safe` and the new proofs out of its proof. Once this example is proved, a restart
step can move into linkv3p's schedules.

## The example

`examples/etcd/restart` is putget3 with a restart:

1. Start members 1, 2 and 3 of a new cluster, with linkv3p's snapshot settings (`SnapCount =
   SnapCatchUp = 1`, `common.NewMember`'s parameters).
2. Put `k = v1` through member 1.
3. Stop member 3, and close its peer listener, its client listener and its gRPC server.
4. Put `k = v2` through member 1, then enough further puts that member 3's last log index falls
   below the leader's compacted index.
5. Start member 3 again: the same name, the same data directory, the same addresses, `NewCluster`
   true as before. etcd ignores it once a WAL exists (`bootstrap`: `haveWAL`).
6. Get `k` through member 3. Panic unless the value is `v2`, or the get failed.

Then the closed theorem `restart3_safe` says what putget3's does: the program never panics.

Its Go test checks, with a counting logger like linkv3p's `TestMainRun`'s, that each run exercised
what the example is for:

- the WAL replayed: etcd logs "restarting local member";
- a snapshot found in the WAL: "constructed a snapshot from WAL record";
- member 3 caught up by a snapshot after the restart: a "sending merged snapshot" to it, then
  "applied snapshot";
- the get answered by member 3.

**The listeners need the example's own start function.** `common.NewMember` serves the raft handler
on a listener it does not return (`go http.Serve(l, s.RaftHandler())`). A restart on the same peer
address needs that listener closed first, so the example keeps it. The same goes for the gRPC
server: `common.Serve` keeps nothing.

## What exists (2026-11-02)

| Piece | State |
|---|---|
| `EtcdServer.Stop`, `HardStop`, `stopWithDelay`, `Cleanup` | names-only; no spec (D19m (A): `run` never returns) |
| `run`'s deferred shutdown (`sched.Stop`, `wg.Wait`, `raftNode.stop`, `close(done)`) | not reached: `run`'s `stop` and `errorc` bags carry `False` |
| `raftNode.stop`, `onStop`, `Transport.Stop` and the peers' stops | theorems (`TransportStop.lean`, D43 M5c) |
| The stopping server | stage M6 of `notes/membership-plan.md`: planned for the removed member's own stop only (Q4 (A)), not started |
| `bootstrap` | names-only, behind `bootstrapContract` (a premise of `NewServer.spec`, so of every closed theorem), whose `bootOk` describes only a new cluster's first start |
| The WAL (`storage/wal`) | names-only, 0% verified (`etc/verified-code.py`, 2026-11-02) |
| The backend's contents across a close and a reopen | not modeled: the backend's model is per incarnation (bbolt's boundary axioms) |
| `raft.RestartNode` | spec on fresh storage only (`bootStorage`: index 0, empty hard state; stage U8) |
| Restoring the stores from a backend | proved for the snapshot install: `mvcc.store.Restore`, the lessor's, auth's, alarm's and membership's `Recover`s (axioms or theorems, D22 S6-S8) |
| `mvcc.New` over a backend with data | `store.restore` proved (restore R4-R5f) |
| `grpc.Server.Stop`, `net.Listener.Close`, closing an `http.Serve` | no spec |
| The durability work (the user's) | reshaping the image certificate `srvImage(R)`; `merged_image` waits on it (`notes/decisions.md`, 2026-10-31) |

## What is new, by layer

**L0. The Go program and its test** (cheap, first). The program and test above, the translation,
and the Go test's counts. No proof.

**L1. Stopping a member.** `HardStop` (or `Stop`, Q1) from the application:

- `run` returns, and its deferred shutdown is proved;
- requests in flight finish with `ErrStopped`;
- the stop gives back what the server held: the thread tokens and reader slots its goroutines
  borrowed, the peers right, the listeners' addresses (`netAddrFree`), and the data directory.

This is M6 of the membership plan, extended from the removed member's own stop to a stop the
application asks for (its Q4 (B)). M6 is the largest stage there: every request path's spec gains
the "server open" token (D19m (B)). It is a prerequisite of both tracks, so it is done once (Q5).

**L2. What one incarnation leaves the next: the durable image.** On a stop, the stopping
incarnation hands over a ghost image of its data directory:

- raft's hard state, log and last snapshot record (the WAL);
- the backend's buckets at its consistent index (the bbolt file);
- the member's id and the cluster id (the WAL's metadata).

The next `bootstrap` consumes the image. A graceful stop in the same process needs no crash
semantics: every write the first incarnation made is visible to the second, fsynced or not. Q4 is
how files are modeled.

**L3. Booting from the image** (`bootstrapContract`'s restart case). On a data directory holding
an image, `bootstrap` returns a record whose `bootOk` describes the restart:

- the `MemoryStorage` holds the image's snapshot, entries and hard state (`ApplySnapshot`, then
  `SetHardState` and `Append`, as `bootstrappedWAL.MemoryStorage` does);
- raft starts with `RestartNode`;
- the backend holds the image's buckets;
- the cluster comes from the WAL's metadata and the backend.

This stays a contract (a premise) as today's `bootstrapContract` is, unless Q3 chooses to translate
`bootstrap` and give the WAL axioms. Its test is the Go test plus the axiom review (the `axiom`
skill).

**L4. Raft: a node restarting from its durable state, in a running cluster.** This is the raft core
of durability:

- `RestartNode` on a storage that is not fresh, with a token for the node's own durable state
  (`nodeFounder` and `nodeJoin` today);
- the protocol invariant must allow a node's volatile state to reset while the others run: its
  commit index may restart lower (a commit-only `HardState` is not written before the next
  `Save`), and its progress and leader knowledge are lost.

`notes/raft-durability-plan.md` §7 has the traps (Q2, Q3), but the user said the durability proof
will be done differently. Q2 is how L4 relates to that work.

**L5. The server over a restart boot.** `NewServer.spec` without the fresh-start premises:

- the apply thread starts at the consistent index (`bootOk`'s `Hthr`, no longer at `0`);
- the committed entries above it are replayed;
- the KV model starts at the image's state: the snapshot install's `kvApplied_of_jump` and
  `snapRecv_kv_jump`, reused;
- the lessor, auth, alarm and membership stores come from the backend (the snapshot path's
  `Recover` specs, reused);
- `%Hrms0` goes: a restarted member's transport adds its peers from the cluster, not from the
  bootstrap peers.

This is stage S-l of the snapshot track (`bootOk` without `%Hnosnap`), widened from a snapshot at
boot to any image.

**L6. Catching up after the restart.** Already proved for a running member: entries, or a snapshot
(`sendMergedSnap`, `applySnapshot`), modulo `mergedCreate_window` and `merged_image`, which the
`snap-window` session is working on. Nothing new is expected here, except that the image the
leader sends is checked against a member that restarted (L4's invariant).

**L7. The example's proof and closed theorem.** As putget3's, plus the stop, the image and the
second start.

## The top-level statement (draft for Scope)

```lean
theorem restart3_safe ... :
    -- putget3's premises (the package assumptions, `ContextReadErrs`, `ContextErrsClient`, the
    -- boot facts, the environment premises), for both of member 3's incarnations
    ... →
    -- the restart contract (L3), if Q3 keeps `bootstrap` a contract
    restartPremise ... →
    -- the step bound, as putget3's
    n + 2 ≤ 2 ^ 28 →
    goose_adequacy ... restart3.Main ... (fun v => v = #())
```

What stays out: crashes (Q4; a later stage, R6 under "Stages"), membership changes (the membership
track), restarting the leader mid-request (Q6), and a member whose data directory was lost.

## Questions for the user (decided 2026-11-02: each the recommended option)

The stop is `HardStop` (Q1). `run`'s deferred shutdown stops the raft node and the transport and
calls `Cleanup`, which closes the lessor, the KV store, the auth store and the backend (etcd's embed
calls `Cleanup` itself only for a server that never started). `Cleanup` must not be called again
after a stop: a second `lessor.Stop` closes a closed channel. L1's stop spec covers `run`'s
shutdown with `Cleanup` in it.


- **Q1. `Stop` or `HardStop`?** `Stop` first tries to transfer leadership
  (`TryTransferLeadershipOnShutdown`), which needs raft's `TransferLeadership` in the server's
  proofs. *Recommended:* `HardStop` first, and stop a follower, so no transfer is attempted. `Stop`
  of a leader is a later widening.
- **Q2. How L4 relates to the user's durability work.** L4 is that work's raft core: a node
  restarting from what it persisted. *Recommended:* L4 is done there, or after it, and this plan
  states only what the example needs of it. Until it lands, the plan's Draft can state `RestartNode`
  over a durable-state token, with its proof a named `sorry`.
- **Q3. `bootstrap`: a contract or a proof?** *(a)* Keep `bootstrap` untranslated and extend
  `bootstrapContract` with the restart case: one premise, reviewed with the `axiom` skill and
  tested in Go. *(b)* Translate `bootstrap`'s restart path (`bootstrapWALFromSnapshot`,
  `recoverSnapshot`, `bootstrapRaftFromWAL`, `bootstrappedWAL.MemoryStorage`) and put the WAL behind
  trust-boundary axioms (`wal.Open`, `ReadAll`, `ValidSnapshotEntries`, `SaveSnapshot`, `Save`).
  *Recommended:* (a) first, as today's boot. (b) is a later stage that moves the trust boundary
  down to the WAL.
- **Q4. How files outlive an incarnation.** *(a)* A ghost image (L2) handed from the stop to the
  next `bootstrap`: no file system model. *(b)* The `osfs` extension (`notes/osfs-ext-plan.md`), or
  `durableExt`, under the WAL and bbolt. *Recommended:* (a), graceful stops only. (b) belongs with
  crashes and the durability work.
- **Q5. M6, the stopping server, is shared with the membership track.** *Recommended:* do it here,
  first and for both: the application's stop (Q4 (B) of the membership plan) and the removed
  member's stop are one shutdown proof with two triggers. Change the membership plan's Q4 to (B)
  once this is accepted.
- **Q6. Which member restarts.** *Recommended:* a follower (member 3, the client on member 1), so
  that no election is forced. A restarted leader is a later widening.

## Stages

- **R0. Scope** (this note): Q1-Q6 with the user; the configuration and the top-level statement
  fixed.
- **R1. The Go program and its test** (L0): translated; the test's counts show a WAL replay, a WAL
  snapshot found, and a snapshot sent to and installed by the restarted member, in every run.
- **R2. Draft, top-down:**
  - `restart3_safe` and the example's specs;
  - `HardStop.spec` and `run`'s return (L1);
  - the image (L2) and the restart contract (L3);
  - `NewServer.spec` over a restart boot (L5);
  - the raft statement L4 needs (Q2).

  Proofs `sorry`, links generated, the glue proved: the example's `Main`, the server's start and
  stop.
- **R3. Review:** fresh `spec-reviewer` rounds on the stop spec, the restart contract and the
  `NewServer` widening, until nothing first-tier is left. Contracts go to the `axiom` skill.
- **R4. Test:** the Go test, and the spec-guided tester on the restart contract (L3), whose
  falsity would be silent.
- **R5. Probe:** one easy proof (the example's `Main` over the frozen specs) and one hard one (`run`'s
  deferred shutdown, or the apply thread's start at the consistent index).
- **Freeze, then Prove:** M6's request-path tokens, L5's widening, the example.
- **R6, later: crash durability** (added 2026-11-03, the user's request). R2-R5 cover a graceful
  stop in one process, where every write is visible to the next incarnation, fsynced or not (Q4
  (a)). R6 replaces the stop by a crash: the process is gone, and only what was fsynced survives.
  The goal is the server-level counterpart of `kvdurable_porcupine_safe`: acknowledged writes
  survive a member's crash and restart, and the history stays linearizable across it.
  - **What it builds on.** Raft's durability, proved with no sorry (durability stage II:
    `StartNode`, `RestartNode`, `node.run`'s persist-before-send, `examples/raft/kvdurable`). R2b-1's WAL
    model, contract and durability invariant (`storage/WalRecs.lean`, `etcdserver/WalApi.lean`,
    `etcdserver/InvWal.lean`, a failed `Save` leaving `walFailed`). R2-R5's restart boot and
    catch-up.
  - **What is new.**
    - File semantics with crashes under the WAL and bbolt (Q4 (b)): the Linux file extension of
      `notes/osfs-ext-plan.md` (files, fsync, bytes lost on a failed fsync) or `durableExt`. The
      image L2 hands to the next incarnation becomes the durable part of the files, not the ghost
      image.
    - The WAL over those files: `Save`'s and `SaveSnapshot`'s fsyncs, the segment cut and rename,
      preallocation. Either proved (Q3 (b), the trust boundary down to the WAL), or a crash-aware
      contract reviewed with the `axiom` skill.
    - bbolt's commit (data pages before the meta page) over the same files, which the osfs plan
      targets. The backend's consistent index is committed with batches, not per apply, so after a
      crash the backend may be behind the WAL; the restart replays the WAL above it. The image
      invariant must say so.
    - The snapshot files (`.snap`, the `.snap.db` backend) against the WAL's snapshot records: their
      order of writes and fsyncs. The two WAL non-issues of R2b-1
      (`etcd-wal-stale-entries-above-snapshot`, `etcd-wal-snapshot-record-order`) are where it
      already showed.
    - The server's persist-before-send. A follower saves before it sends. The leader sends its
      messages before its own `Save` (`raft.go`, "the leader can write to its disk in parallel with
      replicating", raft thesis §10.2.1), so the leader's acknowledged writes rest on a quorum of
      followers' fsyncs, not its own. The invariant must state which, as raft's stage II does for
      raft.
  - **The example**: `restart3` with a crash of the follower in place of `HardStop`, or a crash
    step in its schedule; a closed theorem that the client's history is linearizable, as
    kvdurable's.
  - **Questions for its Scope**: osfs or `durableExt`; bbolt and the WAL proved over the files or
    behind crash-aware contracts; one member's crash or the whole cluster's (power loss); a failed
    fsync handled (`walFailed`, osfs's lost bytes) or excluded by a premise.
  - **Order and size**: after R2-R5 have landed and the osfs extension exists. The largest stage of
    this plan.

## Size and order

- **Largest:** L1 (M6: every request path gains a token) and L4 (raft's restart, the durability
  work's).
- **Moderate:** L5 (mostly the snapshot install's restore, reused) and L3 (a contract, unless Q3
  (b)).
- **Small:** L0, L2 and L7.

R1 can start now. R2 can start once Q1-Q6 are answered, with L4 as a named `sorry` if Q2 says the
durability work comes first.

## R1 (2026-11-02)

- `examples/etcd/restart` (`restart3.go`): `Run(lg)` is the program at a logger, `Main` is `Run` at
  `zap.NewNop()`, so the test counts through `Run` what the proof is about. Two changes to the
  draft above, both from the test:
  - **The stop is `HardStop` alone.** `run`'s deferred shutdown calls `Cleanup`, and a second
    `Cleanup` panics (`lessor.Stop` closes a closed channel). The first version called both.
  - **The member stopped is a follower:** member 3, or member 2 if member 3 leads (Q6; the client's
    member 1 is never stopped). With member 3 always stopped, a run in which it led failed its next
    put ("leader changed") and ended without the check.
- `common.BuildServer` (exported): `newServer` with the auto-compactor off, serving nothing, so that
  `restart3` keeps its listeners and closes them at the stop. Translated, no spec yet (R2).
- The test (`TestRun`) counts, with a counting logger, the restart's messages and fails unless a
  member restarted from its WAL, its WAL held a snapshot, and a snapshot was sent and installed
  after the restart; then it reads the last put's value at members 2 and 3. 15 runs of 15 passed
  (about 1.3s each), each with exactly one restart, one WAL snapshot and one snapshot sent and
  installed after it.
- Translated: project `restart3` of `etc/goose.py`; its package fact `True`
  (`Proof/.../restart3/Base.lean`) and its generated `Init.lean` (`etc/gen-init.py`'s `ROOTS`).


## R2, the Draft: its sub-steps (2026-11-02)

Top-down, each a Lean draft (statements, proofs `sorry`, the glue proved) reviewed before the next
one freezes:

- **R2a. The example's layer.** The specs of `restart3`'s functions (`put`, `startMember` in its two
  uses, `stop`, `Run`, `Main`) and the statement of `restart3_safe`, over the server's interface as
  the example sees it:
  - `common.BuildServer.spec`, `newServer`'s at the auto-compactor off, for a first start (proved
    from `newServer.spec`) and for a restart (over R2c's boot);
  - `EtcdServer.HardStop.spec`: from what the main thread holds of a started member (`memberUp`), to
    what the next incarnation boots from (`memberDown`: the image's token, R2c, and the member's
    addresses back);
  - the trust-boundary specs the stop needs: `grpc.Server.Stop`, `net.Listener.Close` (giving back
    `netAddrFree` and, for the peer listener, the raft protocol's registration, so that the next
    `http.Serve` can register its handler).
- **R2b. The stop (L1, M6).** `HardStop` over `run`'s return and its deferred shutdown, the "server
  open" token in the request paths.
- **R2c. The image and the boot (L2, L3).** The image's ghost token, the restart case of
  `bootstrapContract` and its `bootOk`.
- **R2d. `NewServer` over a restart boot (L5).**
- **R2e. Raft's restart (L4).** `RestartNode` over a durable-state token, a named `sorry` until the
  user's durability work gives it.

What drafting has found so far:

- **Request ids across incarnations.** A restarted member's id generator starts again at its old
  prefix, from the wall clock (`nonissues/etcd-request-id-restart-reuse.md`). The cluster's map of
  issued ids (`idClusterInv`) cannot take a reissued id, so the restart boot takes a premise: the
  new generator's first suffix is past the ids the member's prefix issued (a time premise, as the
  issue's precondition). Named in R2c.
- **The stopped incarnation's goroutines.** `http.Serve` returns at the listener's close without
  waiting for its handlers, and `gs.Stop` cancels the gRPC handlers without waiting for them (grpc's
  default, without `WaitForHandlers`).
  Their loans of the old server's resources are never returned. Nothing needs them back: the next
  incarnation has its own. Only the addresses' rights must come back (R2a's trust-boundary specs).
- **An address is listened on once in a run** (`Proof/net/InvNet.lean`: `net.Listen` consumes
  `netAddrFree` for good), and a gRPC address's server is fixed forever (`grpcServes addr ...`).
  So `restart3` serves only member 1's gRPC API before the restart, and the restarted member's after
  it: its client address is listened on once (changed in the Go program, 2026-11-02; the test
  passes as before). The peer address must be listened on twice. That needs one change to the
  network's trust boundary, drafted in R2a: `net.Listener.Close` gives back `netAddrFree` and the
  right to serve the address with its raft protocol (`httpProtoOwn`). The protocol itself stays
  fixed (`httpProtoAt`: the restarted member serves the same member's raft handler protocol). The
  axiom review (the `axiom` skill) checks it with the old `http.Serve`'s handlers still running.

### R2a, where it stands (2026-11-02)

Drafted, built, no `sorry`, no new axiom. The new server statements are `opaque` placeholders, the
draft statements are `Prop`s the proofs take as hypotheses, and the specs take the thread and
receipt bounds as instances (`ThreadBoundLe`/`ReceiptBoundLe`; `etc/bounds-check.py` stays at its
baseline):

- **Server vocabulary** (`etcdserver/InvRestart.lean`, opaque until R2b/R2c):
  - `srvStopRight s γ id`: `NewServer` gives it, `HardStop` takes it.
  - `srvDiskImage γ id`: the stopped member's data directory.
  - `srvRestartBoot`: the restarted member's ghost bundle (removed in the glue step below: the
    image carries it).
  - `bootstrapRestartContract`: `bootstrap`'s restart case.
- **`EtcdServer.HardStop.spec`** (draft): from `srvStopRight s γ id` and the server's request view
  (`isServerReq`, which `Start` returns: a `HardStop` before `Start` blocks forever; R2b checks only
  `Start` gives it) to `srvDiskImage γ id`.
- **`common`:**
  - `BuildServer.spec`, proved over `newServer` and linked.
  - Its drafted variants `specStop` (with the stop right) and `specRestart` (from the image).
  - `memberBuilt` now takes the apply thread's starting state, a first start's by default.
    `Restart.lean` has `bootPremiseR` and `memberBuiltR` (`memberBuilt` at some starting state).
  - `StartStop.lean`: `Start_builtR_spec`, the restart's `Start`. `Start.spec` takes `ai₀ = 0`, so
    this is a hypothesis until R2d.
- **The network's draft boundary** (`Proof/net/http/ListenerClose.lean`):
  - `registerClosable_spec`: the registration keeps a closing half, and the listener has a
    dynamic type.
  - `ListenerClose_spec`: `Close` gives back `netAddrFree` and `httpProtoOwn`.
- **`restart3`:**
  - `Defs.lean`: putget3's pure facts with `common.httpURL`; `premises` with the restart contracts
    of members 2 and 3; `memberStop`.
  - Specs of `startMember` (`spec`, `specRestart`), `stop`, `serveClient`, `Run` and `Main`.
  - Proved over those specs: `startMember` (both cases), `stop`, `serveClient` and `Main`.

**Next (done 2026-11-02, below):** `Run`'s glue, which is where R2c starts.

### R2: `Run`'s glue and R2c's first design (2026-11-02)

`restart3`'s glue is proved over the drafted server specs: `Run`, `restartCheck`, `put`, `stop`,
`startMember` (both cases), `serveClient`, `Main`. No `sorry`, no new axiom; the server statements
are still the R2a placeholders and hypotheses (`HardStop.spec`, `BuildServer.specRestart`,
`Start_builtR_spec`, the listener-close boundary).

- **The Go program**, two changes (the test passes, 5 runs of 5):
  - The put before the stop is of another key (`k0 ↦ v1`); the check is still on `k`, so a restarted
    member that missed the puts made while it was stopped finds no value and the check panics. Until
    then both puts were of `k` (`v1`, then `v2`), which `putGetInv` (one key, one value) cannot
    take: a persistent `v1` update may fire after `v2`'s. `client.client_Put_other` (over
    `putOtherAu_of_putGetInv`, `kvOpStep_putOther`) is the put of another key under the invariant.
  - What follows the choice of the follower is a function, `restartCheck(cli, m, name, peer,
    peerAddr, client, cluster, lg)`, called in each branch of the leader test: one spec, generic in
    the member, instead of the rest of `Run` proved twice.
- **R2c, the names across a restart.** The image records the stopped incarnation's request names:
  `srvDiskImage γ ρ id` (`HardStop` from `isServerReq s E ρ` to it). A restart returns new names `ρ'`
  with `restartNames ρ ρ'` (defined, `InvRestart.lean`): equal raft names, KV state ghost variable,
  KV model, issued-id map and id prefix -- what the other members and the clients see. The new
  incarnation's own names (its wait registry, its store's index and certificate maps) are fresh, so
  the server allocates them inside `BuildServer`/`NewServer`; the example supplies only the image.
  `srvRestartBoot` (the example-supplied bundle of R2a) is gone; what it was to hold (raft's restart
  token, the cluster's invariants, the id generator's freshness) is the image's or `NewServer`'s
  restart premise's, R2c/R2d to split. The client's invariant moves to the restarted member's names
  by `putGetInv_st` (it reads only the KV state's ghost variable).
- **Thread tokens.** `Run` takes two: `Serve` keeps member 1's `srvGoRes` (and its token), so the
  restart needs its own. The alternative, `HardStop` returning a token, does not fit: the stopped
  member's token was passed on to the next member's start.
- **Found:** `etc/lean-check.py` hung (30 minutes of CPU, "elaborating line 1") when an imported
  module of the checked file failed to build (a `Spec` file with an unknown constant), instead of
  reporting the error; `lake build` of the import showed it in seconds.

**Open in R2c** (the content of the placeholders): the floor fact of the member's id prefix
(`Φs pfx = srvFloorFact E₀` names the first incarnation's stand-in environment; the restarted
member's store is new), the id generator's start past the old ids
(`nonissues/etcd-request-id-restart-reuse.md`), and what the image holds of raft (R2e) and of the
backend (L5).

### R2c: what a restart needs of the cluster's id state (2026-11-02, design)

Drafting the image's content found that three pieces of a member's ghost state, shared with the
cluster, stay with the stopped incarnation for good, so the restarted one cannot be handed them:

1. **Its prefix's entry of the cluster's issued-ids map** (`γi.pfx ↪[γi.cnt] L`): inside the old
   generator's invariant (`idGen`'s `inv idN`). In-flight handlers of the old incarnation can still
   call `Next` after `HardStop` (`gs.Stop` does not wait for them), so the entry keeps growing.
2. **Its prefix's cell of the registries' map** (`idWaitIs γi pfx W`): set once, persistently, to the
   old wait registry.
3. **Its store's index** (`IdxNames`): the authorities are in the old store's lock invariant
   (`store.Close` does not take the lock), and old handlers can still read the store. The restarted
   store's index must be fresh. But the cluster's claim facts are per prefix (`Φs pfx = srvFloorFact
   E₀`, certificates in the first incarnation's index), so a fresh index cannot satisfy the restarted
   generator's `idGen γi g (srvFloorFact E₀')`.

**The fix: key the cluster's per-member id state by incarnation**, a key `(pfx, inc)` in place of the
prefix: the issued-ids entry, the registry cell and the claim facts `Φs` per key, and a claim
records its key. The apply thread already reads a claim's floor only for its own prefix, and uses
the empty floor for another member's ids ("no waiter here", `reqWaitR`); with keys, "own" becomes
"own incarnation", and an old incarnation's replayed entry gets the empty floor the same way. The
store's index, the wait registry and the generator's entry are then new per incarnation, and the
image carries none of them.

**What the keys cannot give: fresh ids.** Two incarnations of one member issue ids under the same
16-bit prefix; the cluster's map must not see one twice. The old generator may keep issuing after
the stop (item 1), so no ghost bound on its suffix exists when the new one starts. Disjointness is
the issue's precondition (`nonissues/etcd-request-id-restart-reuse.md`): the clock does not step back
and the earlier generator, started at millisecond t0, issues in all at most 256·(t1 − t0) ids, t1
the later one's start (2026-11-02 review: the earlier "fewer than 256 per millisecond on average" was
imprecise). It is an assumption about the
environment, and has to enter as a trust-boundary statement or a premise:
- **(a) a spec of the generator's start time** (`time.Now` in `NewGenerator`'s call): the suffix it
  starts from is past every suffix issued under the prefix so far (a per-prefix high-water mark in
  the cluster's invariant), and the old generators stay below the new start. An axiom, refutable in
  a real execution where the clock steps back; recorded with the issue.
- **(b) a premise of the restart** (`bootstrapRestartContract` or a named hypothesis of
  `restart3_safe`): the same, stated over the run's generators.

**Decided (2026-11-02, with the user, after the paper's treatment of `idutil`'s 256-per-millisecond
limit, `/shared/grove-paper/sosp26/case.tex` and `rwmutex.tex`: assume the limit is never reached
where it is reached, keep the specs free of it):** incarnation keys, and the freshness across
incarnations as an assumption at `Next` (`idNoClash`), not a premise of `restart3_safe`. Drafted,
beside the current definitions (nothing uses them yet; no `sorry`, no axiom):

- `idutil/Incarnations.lean` and `etcdserver/InvRestart.lean`: see the review round below for what
  they now hold.

**Next in R2c:**
1. ~~A review of the drafts~~ (round 1 below).
2. The refactor: `IdNames` gains the key, `idClusterInv`/`idGen`/`idClaim` become the keyed ones,
   `NewGenerator`/`Next` re-proved (`Next` over `idNoClash`), the apply thread's case on the claim's
   key in place of the id's prefix (`applyEntryNormal`, two places; `reqWaitR` and `idRegd` restated
   with the own-key claim), each key's facts given at its allocation (`srvFloorFact E₀` of the
   incarnation's store), the examples' allocations (`alloc3`, `memberBoot_of`) through
   `idIncarnation_alloc`, and `Generator.Next` as a trusted model with its `Assume` (the Goose
   configuration's `trusted`, `TrustedCode/`).
3. Then the image's content proper (`bootstrapRestartContract`'s restart case: the WAL, the backend,
   raft's durable state, R2e).

### R2c review, round 1 (2026-11-02, a fresh `spec-reviewer`)

Four first-tier findings on the first draft, all taken:

- **F1: the assumption as a logical statement was refutable** (`idNoClash`, over the keys' map's
  authority: a fabricated map gives `False`; so does a program that makes two generators at one
  time, which the model's arbitrary `time.Now` allows, and adequacy). Replaced by the paper's actual
  mechanism, an `assume` in the semantics: `Generator.Next` becomes a trusted model, its Go body
  followed by `primitive.Assume(issuedBy[id] == nil || issuedBy[id] == g)` over a model-only map. A
  false `Assume` does not return, so the model excludes exactly the clashing executions and no
  statement is left to refute; its faithfulness is the issue's precondition.
- **F2: `Next_specK` had dropped `idCred`** (the receipts' bound that keeps an id out of its own
  generator's list). Restored.
- **F3: `idIncarnation_alloc` was unprovable** (the latest-incarnation map's halves owned by no one).
  The map and `idIncLatest` are gone: a new key's incarnation number is chosen fresh from the finite
  maps, so nothing of the id state is handed from one incarnation to the next, and the image holds
  none of it.
- **F4: a conjunct tying a claim's incarnation to its issuer blocked the claim law.** Dropped (no law
  used it).

Also taken: claims record the claimer's whole key, not its incarnation number, so another member's
claim at the same number is not "own" (F5); the first start goes through `idIncarnation_alloc` too
(F6); keyed `idNoZeroK`, `idWaitTokK_set` (proved), `idWaitIsK_agree` (proved), `idClaimK_agree`
(proved) (F7); each key's claim facts given at its allocation as a saved predicate, not fixed with the
cluster (F8), which removes the store registration (`srvKeyStore`, `srvFloorFactK`: G1, not
usable as written) and the image's incarnation number (G2). The reviewer's answer to whether an old
incarnation's replayed entry can take the empty floor: yes, without the assumption -- a waiter here
holds an own-key claim of its id, and two claims of one id agree.

### R2c requirement from revroom-b (2026-11-05)

The KV invariants now carry size facts (`kvLogSmall γk L := γk.log0.length ≤ 2 ^ 61 ∧ L.length ≤
2 ^ 61`, `InvRequest.lean`; H-rr1, `notes/decisions.md`, "The KV updates hand back the revision
room"), so `kvInv_alloc_boot` (`BuildAlloc.lean`) and `kvInvOn_alloc_boot` (`ServerOn.lean`), and
`kvInvOn_alloc` (`KVAuthModel.lean`), take a premise bounding the start log:
`hsm : γk.log0.length ≤ 2 ^ 61 ∧ γs.raft.boot.length ≤ 2 ^ 61` for the two boot allocations (the
bootstrap log is the invariant's first requested log), `hl0 : γk.log0.length ≤ 2 ^ 61` for
`kvInvOn_alloc` (empty requested log). Any restart-time `kvInv`/`kvInvOn` allocation needs the same:
with the backend's log as `γk.log0`, it discharges `γk.log0.length ≤ 2 ^ 61` from the sole writer's
receipts, `txn.soleWriter_small'` (`log.length ≤ logCh log + 2`, `logCh log < 2 ^ 48`); the
requested log's bound from the cluster's (`readyFits`, `isCommittedLogLb_small`), or as the boot
allocations do, from `receiptBound GF + boot.length ≤ 2 ^ 61`.

### R2c stage 1: the id state keyed by incarnation (2026-11-02, landed)

The refactor's logic, in place (the drafts of `idutil/Incarnations.lean` folded into
`idutil/Defs.lean` and removed):

- **`idutil`:**
  - `IdNames` gains the incarnation number `inc` and the keys' facts map `fs`; `IdNames.key` is
    `(pfx, inc)`.
  - A claim records its claimer's key (`IdClaimV`). `idClaim` is the incarnation's own claim, what
    proposers make and waiters hold; `idClaimAny` is a claim by some key, what a committed entry's
    reader knows.
  - The cluster invariant `idClusterInv issued cnt wn fs Φs` keeps the keys' lists, registry cells
    (its authority moved into the invariant) and the keys' facts' parameters, with one domain for
    the three.
  - The facts are first-order: the cluster fixes a family `Φs : X → …` once, and each key registers
    an `x : X` (`idKeyFactAt`). Saved predicates, the reviewer's F8, would have put the fact under
    two laters. The server's family is `srvFloorFacts`, at the key's store index, and
    `srvFloorFact E` is that family at `E.γ.idx`.
  - Stage 1 keeps one key per prefix in `idClusterOk`, so `Next`'s freshness is still proved from
    prefixes. `idCluster_alloc` makes each member's key `(p, 0)`.
- **The server:**
  - A committed entry carries its claim with the claimer's key and the registration at that key
    (`entryClaim`, `entryWaitOk`, `idRegdAt`).
  - The apply thread cases on the key in place of the id's prefix. With its own key, it reads the
    floor (`idClaim_fact`) and its registration. With another key's claim (another member's, or an
    earlier incarnation's), it reads nothing: `entryRegd`'s "nothing registered" case gives
    `idOther`, and `entryRegd_none_key` turns that into "the key is not mine". A waiter's own claim
    agrees with the entry's, so its key is the incarnation's (`idClaim_agree_entry`).
  - The waiter's `entryWit` and the proposals' mint `srvPropMint` take claims by any key. The mint
    is the cluster's, so a claim stored there at a member's own key would have been stated at the
    wrong key for every other member.
  - `NewServer`'s premise is the keyed invariant at `srvFloorFacts` plus the member's key fact at
    its store index (`E₀.γ.idx`).
- **Left for a cleanup pass:** `memberBoot` and `NewServer.spec` still carry the per-prefix `Φs`
  and its equation `Φs pfx = srvFloorFact E₀`, which nothing reads any more (about 40 files pass
  them).
- **Next, stage 2:**
  - A trusted `Generator.Next`, its Go body followed by `primitive.Assume`, with the issuers' record
    as an extension's state (`GooseLang/Ext/`). Linked results that reach `Next` gain the
    extension's instance, which each example's adequacy provides.
  - Drop the one-key-per-prefix condition, and prove `idIncarnation_alloc` (a fresh incarnation
    number chosen from the finite maps).

### R2e: raft's restart, now that the durability work has landed (2026-11-02)

The durability branch landed on `lean` (stage II (u)), so R2e can be built on proved raft specs,
not a named `sorry`:

- **`RestartNode.spec`** (`Spec/go_etcd_io/raft/v3/RestartNode.lean`, proved). It restarts node
  `id` of the cluster from three things:
  - the id vacant (`nodeVacant`: no node of it runs);
  - a storage holding raft's stored contents `σ` (`restartStorage`), at a configuration point `a`
    the storage's `ConfState` reports, between the applied index and the stored commit;
  - the client's update `AU`, which fires when raft reads the storage. It checks the storage holds
    the client's durable state `S` (`raftState`, `StorageHolds`).

  Its post gives the `Ready` loop's token at the committed log from `max σ.b Applied`. It also gives
  the configuration view at `(a, m)` and the storage's key.
- **`node.Stop`** gives the id's vacancy back (`nodeStopped`, `nodeVacant`).
- **`examples/raft/kvdurable`** is the pattern for a stop and a restart:
  - `Replica.stop` returns `nodeVacant` and the replica's durable-state ghost variable (`raftState`).
  - `Cluster.restart` restarts from them, with the crash token held by the cluster.

For the server, this fixes what the image (`srvDiskImage`) holds of raft:
- `HardStop`'s `run` shutdown calls `raftNode.stop`, which calls `node.Stop`, which returns
  `nodeVacant`.
- The WAL's hard state, snapshot and entries are the durable state `S`. etcd's `bootstrappedWAL`
  rebuilds its `MemoryStorage` from them, so bootstrap's restart contract (L3) must produce
  `restartStorage σ` with `StorageHolds σ S`.
- The configuration point is the WAL snapshot's `ConfState`, the snapshot's index.

The open questions:
1. The server's raft node is not `kvdurable`'s. It runs through `raftNode` and its `Ready` loop, and
   `bootstrap` reads the WAL, not a durable file of the client's. So the restart contract has to
   state the WAL image's correspondence to `S`.
2. `RestartNode`'s scope: the stored commit covers the bootstrap log (`γ.bootLen ≤ σ.commit`). That
   holds for `restart3`, which stops a member only after a put has committed past the bootstrap.

### R2c: the image's content (2026-11-02, draft, `InvRestart.lean`)

What a stopped member's data directory holds, and what `bootstrap` makes of it, read from etcd's
code (`bootstrap.go` at the pin):

- On an existing WAL, `bootstrapRaftFromWAL` gives raft no peers, so `newRaftNode` calls
  `RestartNode`; `raftConfig` leaves `Applied` at 0. The storage is `bootstrappedWAL.MemoryStorage`:
  `ApplySnapshot` of the WAL's last snapshot record, `SetHardState`, `Append` of its entries.
- `bootstrap` then **replaces the WAL snapshot's `ConfState` by the backend's**
  (`buildConfStateFromV3store`). So raft restarts with the membership the backend holds at its
  consistent index `i`, not at the WAL snapshot's index. `RestartNode` allows this: its
  configuration point may be anywhere from the storage's base to its stored commit.
- `bootstrapClusterWithWAL` builds the cluster from its ids only; `Finalize`'s `cl.Recover` reads
  the members from the backend's buckets. No remotes, as on a first start.
- `recoverSnapshot` keeps the backend file unless its consistent index is below the WAL snapshot's
  (then a `.snap.db` replaces it). A graceful stop never leaves it below: a snapshot is of the
  applied state.

**The draft** (statements only; the opaque parts are R2d's or the trust boundary's):

- `srvDiskImage γ ρ id`: raft's part (`nodeVacant`, `raftState S`, the WAL's records `σ` with
  `StorageHolds S σ`, what `RestartNode` takes); the backend's part (the file's data `D` is the
  image of a committed prefix `A` through `i`, the snapshot path's `imageAt`, reused); the order
  `σ.b ≤ i ≤ σ.commit`; the configuration point `confAt γ.cl i m`, `m` the backend's members at
  `A` (`v3ConfState`, opaque until R2d); the files (`srvFiles dd σ D`, a trust-boundary token, and
  the backend path's `pathOwn`).
- `bootOkR`: `bootOk` with five changes marked `[R2c]`: no peers; the storage rebuilt at `σ`
  (`memStorRestarted`, opaque until R2d derives `restartStorage` from it, as kvdurable's
  `kd_restartStorage`); the members `(restModel 0 γ.boot L).mem`; the consistent index loaded at
  `i`; the backend's data the image, the fresh file's facts gone.
- `bootstrapRestartContract`: for every image whose facts hold, `bootstrap` on the files gives an
  error or `bootOkR`. A premise, as `bootstrapContract`.

**What R2b must prove of the stop** (`HardStop` to the image): the raft loop's `raftState` and
`node.Stop`'s `nodeVacant`; the backend's certificate at its consistent index (as the snapshot
sender's, from the store's view and the index's meta keys); the order `σ.b ≤ i ≤ σ.commit` as an
invariant of the raft loop and the apply thread; `confAt` at `i`; and the closes' trust-boundary
axioms giving `srvFiles`.

**Scope:** a static cluster (`Hmembers`, `Hdirps` as a first start's); graceful stops in one
process (no crash: writes are visible to the next open, synced or not).

### R2c image review, round 1 (2026-11-02, a fresh `spec-reviewer`)

The reviewer confirmed the order `σ.b ≤ i ≤ σ.commit` at a graceful stop from etcd's code:
- The raft loop hands a `Ready` to the apply thread before its `Save`, with no stop check between.
- The stop runs the scheduler's pending jobs (`sched.Stop`) before `s.r.stop()`, and closes the WAL
  after the loop exits.
- The backend's last commit (`CommitAndStop`) saves the consistent index.
- A WAL snapshot record follows its `applySnapshot` job. etcd's own comment that the consistent
  index may pass the commit is about crashes only.

It found no bug in etcd. Its first-tier findings, all taken:
- **F1.** `bootOkR`'s `ciApplying` at the image's index was false: the applying index and term are
  the apply loop's own fields, which `NewConsistentIndex` leaves at 0. Back to `0 0`.
- **F2.** The image's directory was existential, unrelated to the configuration's `DataDir`. Now a
  parameter: `srvStopRight s γ id dd` records it at `NewServer`, and `srvDiskImage γ ρ id dd`
  names it. `HardStop` and `stop` quantify over it; the examples' specs give `name ++ ".etcd"`
  (`cfgOk`).
- **F3.** The restart could not give `memStorRegAuth ∅`: raft's names are kept, so the registry is
  the first incarnation's, its old storage registered for good. Now the image carries the
  registry's authority back, and the contract takes it at any `M` and returns it with the new
  storage at a location not in `M`.
- **F4.** Nothing made the stopped member have applied the bootstrap log. In `restart3` the put
  returns on two members' acknowledgements, so a follower may be stopped before its first `Ready`.
  Then the members bucket is empty, and `Hmem`, `Hmembers` and `RestartNode`'s
  `bootLen ≤ σ.commit` fail. Now `γ.cl.bootLen ≤ i` is in the image and the contract's premise: a
  scope restriction `restart3`'s stop must meet (R2b: a witness that the member applied
  `bootLen`). `v3ConfState` is now over the backend's data (the members bucket), as
  `buildConfStateFromV3store` reads it.
- **F5.** The KV names' `c0` was free in the contract, but `restModel (W64 0)` assumes 0. The
  contract now asks for an image at `c0 = 0` (existential), the image states `ρ.rd.kv.c0 = 0`, and
  `restartNames` keeps `c0`.

Second tier:
- **Taken:**
  - `srvFiles` names the member (the WAL's metadata, `cv.ID' = id`).
  - The contract's image is an existential.
  - `ctxs` is dropped from the contract.
  - The error arm is documented: like a first start's, the contract may always fail.
- **Open:**
  - `srvFiles`'s exclusivity per directory (R2b makes the token).
  - `ctxs` is still a dead parameter of `bootPremiseR`.
  - Sealing the image behind an API module with the laws R2d needs (the image is an exposed `def`
    today).
  - `memStorRestarted` must also give the snapshot token and the storage's conf state, which
    `restartStorage` needs (R2d).
  - Conf entries in `(σ.b, i]` are delivered again after a restart. etcd skips `ApplyConfChange`
    for them but still calls `AddMember`/`SetConfState`; R2d must check that an `AddMember` of a
    present member is harmless.

### R2c stage 2: the trusted `Next`, design (2026-11-02)

- **The record: an extension.** `idutil` has no package variable whose initializer could allocate a
  model-only map, and `go.GlobalAlloc` runs only from an initializer. So the issuers' record is a
  GooseLang extension's local state, `idIssueExt` (`GooseLang/Ext/IdIssue/`): a map from id to
  issuing generator.
  - Its one operation, `"Issue"` of `(id, g)`, returns whether no other generator holds the id
    (`M !! id = none ∨ M !! id = some g`), and records `id ↦ g` if so.
  - The examples close their programs over it in place of `trivialExt`. It does nothing a Go
    program can see.
- **The model: `Generator.Next`, trusted.** It is the generated body with one step before the
  return: `assume (ExternalOp "Issue" (id, g))`. Perennial's `assume` loops forever on `false`
  (`wp_assume`), so the model excludes exactly the executions in which two generators issue one id.
  Its faithfulness is the issue's precondition. It goes through the `axiom` skill's review before it
  lands.
- **The proof: two atomic steps.**
  - The increment counts the id as pending in the generator's invariant (`idIssued` is the list
    plus the pending ids).
  - The issue step opens the cluster invariant. Its `assume` gives `M !! id ∈ {none, some g}`.
    `some g` would put the id in the generator's own list, but a pending id is not there: the
    receipts' bound keeps the suffix from wrapping. So `M !! id = none`, the id is in no key's
    list, and it enters the maps.
- **The cluster invariant:**
  - The extension's record (the program's half). It agrees with the keys' lists through a map from
    key to generator, `Gm`.
  - `Gm` is injective. That is proved at registration: the new generator's fields are owned whole,
    and every registered generator's prefix field is persistently readable, so the new address
    differs from them.
  - The stage-1 condition, one key per prefix, goes. `idIncarnation_alloc` becomes provable: a fresh
    incarnation number, chosen from the finite maps.

### R2c stage 2, where it stands (2026-11-02)

**Done, and it checks:**
- The extension: `GooseLang/Ext/IdIssue/Impl.lean` (`"Issue"` of `(id, g)`) and `Specs.lean`
  (`wp_IdIssue_atomic`, the closure `idIssueExts`).
- The trusted model `TrustedCode/go_etcd_io/etcd/pkg/v3/idutil.lean`: the generated body with
  `assume (Issue (id, g))` before the return.
- The Goose configuration marks `Generator.Next` trusted; the translation was regenerated, with its
  `ManualProof` module.

**Then, in order** (all done 2026-11-02):
1. **The record's ghost state, in a form that needs no `Main` changes** (`GooseLang/Ext/IdIssue/Specs.lean`):
   - The state interpretation holds a ghost record contained in the physical one (any initial
     record is allowed; the ghost one starts empty), its authority and every entry's persistent
     element. The program starts with `True`, so no `Main` takes anything for it.
   - `wp_IdIssue` gives, with `b = true`, the fact `idIssueFrag id g`, with the mask open around the
     step for an invariant. `idIssueFrag_agree`: one issuer per id.
   - `idIssueFragD` reads the fact without the instance: `if h : HasExt idIssueExt then … else
     False`, rewritten by `idIssueFragD_eq` under the instance. `idIssueFragD_agree` holds either
     way. So no spec mentions the instance; only proofs that run `Next` take it.
2. **`idutil`** (`Defs`, `Lemmas`, `NewGenerator`, `Generator__Next`):
   - `IdNames` gains `pend`. A key's entry of the keys' map is a pair: issued ids, and the generator
     once `NewGenerator` registers it. That replaces the separate key-to-generator map.
   - The cluster invariant keeps, per registered key, its generator's persistent prefix field and
     the record's fact for every listed id (`idKeyGenFacts`). One key per generator (`idClusterOk`).
     The one-key-per-prefix condition is gone.
   - `NewGenerator` registers its generator. It is no registered key's: its prefix field is owned
     whole, and `w64_pointsto_excl` is a local lemma, recorded in `notes/perennial-changes.md`.
   - `Next` is proved over the trusted model in two steps:
     - the increment counts the id as pending and takes its wait slot;
     - the issue step opens both invariants around `"Issue"`. With the record's fact, the
       generators' facts, the injectivity and the pending token, the id is in no key's list, so in
       no map.

     The proof depends only on Lean's standard axioms (`#print axioms`).
   - `idIncarnation_alloc`: a key `(p, inc)` with `inc` above every key's (`idKey_fresh_inc`), its
     empty entry, registry cell and facts' parameter. R2c's restart allocation will use it.
3. **The allocations**: the `IdNames` literals take `pend`; the server's member allocations
   (`NewServerAlloc`, `NewServerAllocOn`) allocate the pending map; the boot statements' entries are
   pairs. `SrvRaftLog`'s `srvRdFresh_mint`, which opens the generator's invariant, has its new shape.
4. **The instance.**
   - `Next.wp_proof` takes `[HasExt idIssueExt]`, and so does every result that reaches it:
     `etc/gen-link.py` adds it to the modes linking over the server (`EXTS`: server, v3rpc, common,
     linkv3p, linkvtxn, watchkv, authkv, cachekv, k8setcd3, k8s, k8s-etcd3), and the hand-written
     sections using those results (`Results` files, the examples' `Main`s, ...) have it as a
     section variable. A file was given it only where the build asked for it.
   - The examples' closure (`TrivialExt.lean`, names kept) is `[idIssueExt]`, with
     `trivialExts_hasExt`. The adequacy files take the universal camera they already had as the
     extension's pre-ghost state (`goosePreGExts := (⟨…GF_allG⟩, ())`) and the closure's `HasExt`
     as a local instance.
5. **Review** (a fresh agent, the trusted-base and `axiom` skills' method): verdict OK, nothing
   unsound. The trusted `Next` is the generated body plus the one `assume` step; the record's step
   is deterministic, heap-preserving, and stuck only off its one call site; the assumption yields
   only "two generator addresses never issue one id", and the proof does not use the record against
   a single generator's repeats (those are excluded by the receipts' bound). Documentation fixes,
   applied:
   - The precondition was stated imprecisely ("fewer than 256 ids per millisecond on average"): the
     exact one is that the earlier generator, started at millisecond t0, issues in all at most
     256·(t1 − t0) ids, t1 the later one's start. Corrected in the issue, the model, the extension
     and this plan.
   - The issue file's "How the proof handles it" was stale (pointed to `Incarnations.lean` and
     `primitive.Assume`); `TrivialExt.lean`'s header said the closure does nothing.
   - The crash rule's limit (a generator after a crash could take a stopped one's address: still
     sound, but `Next`'s proof would need the record cleared) and the extension's non-package name
     are documented in `Impl.lean`.

### R2b: the stop, its plan (2026-11-02)

`HardStop` sends on `s.stop`; `run` returns and its deferred shutdown runs: `close(stopping)`,
`cancel`, `sched.Stop()` (the pending `applyAll` jobs run), `s.wg.Wait()`, `s.r.stop()` (the raft
loop's `onStop`: `node.Stop`, the ticker, the transport, the WAL's `Close`), `Cleanup()` (the
lessor, the KV store, the auth store, `be.Close()`, the compactor), `close(done)`; `HardStop`
returns on `done`. What the proof has today: `run`'s `stop` and `errorc` bags carry `False` (D19m),
so the shutdown is unreached; `raftNode.stop`'s post is `True`; `Cleanup` has no spec; the WAL is
the trust-boundary contract `isRNWal` with an open token (`walOpen`) and no contents.

Two findings from reading the stop path:

1. **The raft loop can stop holding an unsaved `Ready`.** `raftNode.start`'s loop returns on
   `r.stopped` from two selects between receiving a `Ready` and its WAL `Save`: the read state's
   send (`readStateC`) and the hand-off to the apply thread (`applyc`). The server's proof enters
   each batch at its receive (`rnBusyN`: "its WAL `Save` is not modelled as durable"), so at such a
   stop the node's durable state `raftState S` includes a batch the WAL never got, and the image's
   `StorageHolds S σ` is false. Raft's node API allows the other order (`readyEnter`: "a durable
   client: in the write that makes it durable"): what the loop does before the `Save` needs only
   the receive (the committed entries and `isCommittedLogLb` for the apply thread; at role leader
   the messages, `readyLeaderMsgs`). So R2b moves the server's *enter* to the WAL's `Save`. Not an
   etcd bug: at such a stop nothing of the batch was applied (the stop is chosen instead of the
   `applyc` send) or sent by a follower (it sends after the `Save`); a leader's messages carry no
   promise.
2. **The WAL's records are not modelled.** The image needs them (`σ`, what `ReadAll` returns from
   the last snapshot record). They become a ghost token beside `walOpen`, `walRecs w σ`, which the
   trust-boundary contract `isRNWal` updates: `Save(h, es)` (the entries truncate-and-append, the
   hard state replaced when not empty) and `SaveSnap(m)` (a snapshot record: `ReadAll` then starts
   there). Two threads write the WAL: the raft loop (`Save`, `SaveSnap` of a received snapshot) and
   the apply thread (`SaveSnap` of its own snapshots, `snapshot()`), so the token lives in an
   invariant both open; the raft loop's `Save` fires *enter* inside it, keeping
   `StorageHolds S σ` (as `kvdurable`'s `kdFileInv`).

The sub-steps, each a draft reviewed before its proof:

- **R2b-1. The WAL as the durable point.** `walRecs` and its laws, `isRNWal`'s `Save`/`SaveSnap`
  over it (trust boundary), `bootOk`'s fresh WAL's records (`StorageHolds RaftState.init σ₀`), the
  invariant `S`–`σ`, the raft loop entering at the `Save` (`raftNode.start`'s proof). The order's
  first half: every WAL snapshot record is at or below the applied index (`σ.b ≤ i`: the raft
  loop's `SaveSnap` of a received snapshot precedes its apply; the apply thread's own snapshots are
  of its applied state), and its second: the apply thread applies only entries a saved hard state
  commits (`i ≤ σ.commit`, the `Save` follows the hand-off unconditionally).
- **R2b-2. The shutdown.** `s.stop`'s bag carries the stop request; `done` closes with the image
  escrowed for the stop right's holder (an invariant: the image or the claim); `run`'s stop case
  through the deferred shutdown: `sched.Stop`'s last post (the apply thread's final state: its
  index `i`, the backend's view), `s.wg.Wait`, `raftNode.stop` (its post strengthened: `raftState`,
  `nodeVacant`, the WAL closed with its records), `Cleanup` (its spec: `be.Close` gives the data
  `D` the store's view held and the path back). `HardStop` proved; `srvStopRight` defined (the
  stop request and the claim, the directory recorded).
- **R2b-3. The image.** The closes' trust-boundary axioms giving `srvFiles dd id σ D` (`wal.Close`
  and `backend.Close` in one directory, its exclusivity the right's); the backend's certificate at
  the consistent index (`imageAt`, as the snapshot sender's from the store's view and the meta
  keys); `confAt` at `i`; the bootstrap log applied (`bootLen ≤ i`: the scope restriction of R2c's
  review F4, which `restart3` meets by waiting, before the stop, until the member has applied it;
  a Go change to the example, and a spec of the wait).

Order: R2b-2's statements first (they fix what R2b-1 and R2b-3 must give), then R2b-1, R2b-3.

### R2b-2: the shutdown's statements (2026-11-02, draft)

Reading `start` changed one thing in the plan: `start`, not `NewServer`, makes the channels `stop`,
`done` and `stopping`, so the stop right comes out of `Start`. `NewServer` records only the data
directory (`srvDataDir s dd`: the read-only `Cfg` field's `DataDir`).

- **The right** (`InvRestart.lean`, defined): `srvStopRight s γ ρ id dd` is the stop channel (a bag
  whose predicate is `True`: anyone may ask), `done` (a broadcast channel whose close announces
  `srvDoneInv γ ρ id dd c`, an invariant holding the image or the claim `c`), and the claim `c`. It
  now records the request names `ρ`, so that `run`, which knows them, can fill the escrow.
- **`HardStop`** (proved; translated with its body, as is `Cleanup`): from the right, the image.
  It no longer takes the request view `isServerReq`: a `HardStop` before `Start` blocks forever,
  which partial correctness allows.
- **`Start`** (`common.Start_builtS_spec`, first start, and `Start_builtR_spec`, a restart: draft
  `Prop`s): from `memberBuilt` and `srvDataDir s dd`, `memberUp` and the right at
  `ρ.rd.raft.raft`. `BuildServer.specStop`/`specRestart` give `srvDataDir` in place of the right;
  `restart3`'s `memberStop` records `ρ`, `stop` no longer takes `isServerReq`.
- **`run`** (`run.specStop`, draft): `isServerRun` takes the stop requests' predicate `SP` and
  `done`'s `DQ` (defaults `False` and `True`, the runs covered so far, unchanged), at `True` and
  `srvDoneInv`, with `srvShutdownPre` (the raft loop's stop claim, the data directory, the storage
  registry's authority).
- **`raftNode.stop.specStop`** (draft): with the loop's stop claim and the apply side's token at the
  log `A` handed to it, the node's id vacant, its durable state `S`, the WAL closed with records `σ`
  (`rnWalClosed`, opaque until R2b-1), `StorageHolds S σ` and
  `σ.b ≤ |pre ++ A| ≤ σ.commit`.

Left to R2b-3's draft: `Cleanup`'s spec (the backend closed, its data), the closes' axioms
(`srvFiles`), and the image's assembly from `run`'s state after the shutdown.

### R2b-2 review, round 1 (2026-11-02, a fresh `spec-reviewer`)

No bug in etcd. Three blocking findings, all taken:
- **F1.** `srvDataDir` made the whole `Cfg` read-only, which contradicts `memberBuilt`'s ownership of
  the fields `start` writes (`SnapshotCount`, ...): `BuildServer.specStop`'s success case was
  `False`, and the proofs over it vacuous. Now per field (`DataDir`, as `srvSnapRes`), with
  `DedicatedWALDir` empty, so that the WAL is `<dd>/member/wal` as `srvFiles` says.
- **F2.** With a stop request carrying nothing, `run` could not fill the escrow: a `HardStop`
  right after `Start` stops a member that has not applied the bootstrap log, and the image needs
  `bootLen ≤ i` (R2c review F4). Now the stop bag carries `srvBootApplied ρ` (an applied-index
  lower bound, `appliedAtLeast`, at least the bootstrap log's length), which `HardStop` takes.
  `restart3`'s `stop` gets it by waiting: `for m.s.AppliedIndex() < NBoot { time.Sleep(1ms) }`
  (Go changed, the test passes; proved, with `memberStop` carrying the applied index's invariant
  and the raft names, `restartCheck` the bootstrap log's length).
- **F3.** Nothing named the sources of the shutdown's resources. `srvShutdownPre` now lists
  `srvCleanupOwn` (the lessor's stop right, the auth store's closer; opaque until R2b-3) besides
  the raft loop's claim, the data directory and the registry's authority, and says where each
  comes from; `NewServer` keeps them for `Start` (`srvStopKeep`, opaque, which
  `BuildServer.specStop`/`specRestart` give and the `Start` drafts take). The KV's and the backend's
  closers come back from the apply thread through `sched.Stop`'s last job's post.

Smaller:
- **F4 (one spec per function), recorded, not yet done:** the drafts are families (`run.specStop`
  beside `spec`, `Start_builtS_spec` beside `Start.spec`, `raftNode.stop.specStop` beside `spec`,
  `BuildServer.specStop` beside `spec`). When R2b-2's proof is done they collapse: `Start.spec`
  gives the right (callers that never stop drop it), `run`'s one spec is the stop-capable one,
  `raftNode.stop.specStop` replaces `spec`. The draft keeps both so that nothing proved moves.
- **F5:** `raftNode.stop.specStop` is true of `raft.go` once the server enters a batch at its WAL
  `Save` (R2b-1). R2b-1 must change `isRaftNode`'s `done` (its predicate is fixed at `True` in a
  persistent conjunct), so every spec over `isRaftNode` moves. The image's order is at the
  backend's consistent index, equal to the handed log's length once the jobs ran and the backend
  committed: R2b-3's. Both noted in the docstring.
- **F6:** `run.specStop` no longer takes `id` (it is `γn.id`). Not taken: dropping `γ` from
  `srvStopRight`, or a `memberBoot` law in place of `startMember`'s unfold (it would rebuild every
  example for one line of glue).
- **Scope:** `run.specStop` covers first starts (`isServerRun`'s `HEr`); a restarted member's
  right is R2d's. The `errorc` path stays closed (its bag's `False`).

### R2b-1: the WAL's records (2026-11-02, blocked on a finding)

Drafting the WAL's records model found that etcd's WAL does not hold the durable state raft's
restart checks. `wal.ReadAll` returns every entry record above its start snapshot's index,
whatever its place relative to the snapshot record. A follower that installs a received snapshot
at `k` over a conflicting log keeps the old entries above `k` in its WAL; if it stops before any
entry above `k` reaches it, its restarted log is the snapshot followed by entries of lower terms
(`nonissues/etcd-wal-stale-entries-above-snapshot.md`, with a failing WAL-level test). Raft's
durable state (`RaftState.next`) has no entries above an installed snapshot, so the image's
`StorageHolds S σ` is false of such a member, and so is `raftNode.stop.specStop`'s post.

Options:
1. **A fix on the goosed fork** (as the three raft fixes): `ReadAll`, at a snapshot record at `k`
   whose term differs from the entry it holds at `k`, drops the entries from `k` on (a received
   snapshot that conflicts; the server's own snapshots match their entry, and raft puts a received
   snapshot in a `Ready` only when it conflicts or the log is shorter). The model of `ReadAll`
   then matches `RaftState.next`, and R2b-1 goes on as planned. Upstream-worthy if the stale tail
   can be shown to matter at the raft level.
2. **Model the WAL as it is:** `StorageHolds` (raft's restart, the durability work) admits a stale
   tail of lower terms above the snapshot. A change to raft's restart spec and its proof (the
   restarted log is not a log raft ever had).
3. **A scope premise** on the stopped member (no received snapshot since its last appended entry):
   nothing in `restart3` can check it.

**Decision (the user, 2026-11-02): option 1, the fork's fix.** Branch `goose-lean-walsnap` of the
etcd fork (`6293455e0`, on the pin `ab3c28d9a`; in `/shared/etcd-goose-lean-walsnap`): `ReadAll`
reads the records as the log they write (an entry at or below the start index truncates the
entries above it; at the start snapshot's record the entries above it go unless the log holds the
snapshot's entry). The WAL and server tests pass; two new tests fail without it. The pin moves to it
once the branch is pushed (`etc/goose.py`, `examples/go.mod`); the Go code is the trust boundary
(the `wal` package is names-only), so the translation does not change.

**The draft** (`etcdserver/InvWal.lean`, imported by nothing proved yet): the records `walRecs`
(trust-boundary token), their model (`walSave`: hard state by `phsNext`, entries by `appendEnts`;
`walSaveSnap`: the entries above the snapshot kept only when the log holds its entry; `walFresh`),
the contract `isRNWalR` (`Save`/`SaveSnap` as atomic updates in the cases the server uses,
`WalSaveOk`/`WalSnapOk`, failing only on I/O), the durability invariant `rnDurInv`, the pure laws
as statements (`walSave_holds_stmt`, `walSnapSave_holds_stmt`, `walOwnSnap_holds_stmt`,
`walFresh_holds_stmt`), and the receive keeping *enter* unfired (`rnReadyRecvR_stmt`).

### R2b-1 review, round 1 (2026-11-02, a fresh `spec-reviewer`)

Code reading found a second etcd problem and a flaw in the first fork fix:
- **G1** (`nonissues/etcd-wal-snapshot-record-order.md`): the apply thread's own `SaveSnap(i)`
  can land after the raft loop's `SaveSnap(k)` of a received snapshot, `i < k`, and
  `recoverSnapshot` opens the WAL at the *last* record: the restart reads back the old log above
  `i` with the commit `k` (a panic if it ends below `k`). Fork fix: open at the highest index.
- **G2**: the first fix decided by the WAL's entry at the snapshot's index, but raft decides on its
  in-memory log. Fork fix revised: drop the entries above the start snapshot iff it is above the
  commit index saved before its record (exactly a received snapshot).
- **G3**: `ReadAll` did not restore `w.state`, which a cut repeats at a file's head (the G2 rule
  needs it). Fixed.
The fork's branch is now `6293455e0` + `ce3dbc097`; the WAL and server tests pass, four new WAL
tests fail without it.

On the draft:
- **F1, F5** (false laws): `walSaveSnap` follows the commit rule and ignores a record below the
  base; `walSnapSave_holds_stmt` and `walSave_holds_stmt` take the entries consecutive, which
  raft's `ReadyRestFacts` does not state yet (a raft API law to add); `walOwnSnap_holds_stmt`
  needs the durable log's term at the snapshot's index, which the invariant must carry.
- **F2**: `WalSaveOk` requires consecutive entries. `Save` failing only on I/O widens the
  environment premise `walSaveOk` (today `SaveSnap`'s only): **open, the user's choice**.
- **F3**: `rnDurInv` needs a "snapshot pending" state, the hard-state agreement, the
  `walCommitLb` authority, the log's agreement with the committed log, an exit for the stop, and
  credits for `walRecs`: listed in its docstring, for the next draft.
- **F4**: entering at the `Save` needs a raft API change: `readyGot` must give
  `deliveredLogLb (delivered ++ ce)` and the new hard state's term fact without *enter* (the
  hand-off on `applyc` precedes the `Save`).
- **F6**: `isRNWalR` replaces `isRNWal`'s `Save`/`SaveSnap` in the proof.

**Decision (the user, 2026-11-02): a failed `Save` leaves the records unknown** (`walFailed`, a
case of the durability invariant), not a premise that `Save` fails only on I/O: the loop then calls
`lg.Fatal`, never returns, and never stops, so no image is made of such a WAL.

**The pin moved** (2026-11-03): the etcd project at the fork's `ce3dbc097` (`etc/goose.py`,
`examples/go.mod`, `examples/k8s/etcd3/go.mod`); the translation changed by the new names-only
`newestSnapshotEntry`.

### R2b-1 draft, round 2 (2026-11-03)

In `etcdserver/InvWal.lean`, after review round 1:
- **Raft's receive** (`readyGotFacts_stmt`, a raft API change): `readyGot` also gives
  `deliveredLogLb` of the delivered log after the `Ready` and its hard state's committed fact
  (`committedAtTerm`), without *enter*. Raft's proof has both, persistent, where it builds
  *enter* (`isCommittedLogLb`, `hsCommitted`, the busy driver's `dlvLb`).
- **The durability invariant** (`rnDurInv`, over the ghost names `WalNames`): until the stop takes
  the contents (its claim), the durable state and either the records holding it (`walHolds`: the
  committed log they are within, with which the durable log agrees, `DurAgrees`; the hard state's
  half; the commit counter) with the pending token, or a received snapshot's records with its
  `Save` pending, or a failed `Save`'s records with the "not failed" token. `walCommitLb` is the
  counter's lower bound. `rnDurTake_stmt`: the stop takes the contents out with its claim and the
  loop's two tokens.

### R2b-1 review, round 2, and the draft's round 3 (2026-11-03)

The model half holds: the pure laws are true as stated (checked by hand against `StorageHolds`,
`RaftState.next`, `appendEnts`), `walSaveSnap`/`WalSaveOk` match the fork's `ReadAll`, and raft's
receive can give the facts the server needs before *enter* (in `readyRecv_open` they are
persistent before `api_enter`), which are enough for the hand-off on `applyc`. The invariant half
was not keepable; round 3:
- **F1, F2:** the pending token excluded the wrong case, and nothing tied the invariant's durable
  state to the loop's. Now a ghost variable, half the loop's, holds the loop's view (`WalView`:
  the durable state, the records' hard state, the pending received snapshot, the handed log), as
  kvdurable's writer variable; the records are as the view says (`walAsViewed`).
- **F3:** `σ.commit ≤ |committed log|` was not keepable (raft pages committed entries). Now the
  handed log `l`: `σ.b ≤ |l| ≤ σ.commit`, `DurAgrees S l`; `walCommitLb` bounds `|l|`.
- **F4:** a failed `Save` now leaves some records (`∃ σ'`), not `walFailed`, so that the apply
  thread's `SaveSnap` can still update them; the taken state holds the apply thread's token.
- **F5:** `walRecs` is a ghost variable at an opaque per-WAL name (timeless, exclusive by proof),
  and the invariant holds `raftState` without an extra later.
- **F6:** the receive statement became `readyGotR`, the receive's new postcondition (a law over
  today's `readyGot` could not be proved).
- **F7–F10:** the consecutive entries come from raft's `readyRest_indices` and `readySnap`;
  `DurAgrees` includes the base; the records' docstring says the restart opens at the highest
  record; `isRNWalR` stands alone (it replaces `isRNWal`'s `Save`/`SaveSnap`).

### R2b-1 review, round 3, and the draft's round 4 (2026-11-03)

The reviewer walked every step (a `Ready` with and without a snapshot, commit-only, empty hard
state, paged entries, a failed `Save`, the apply thread's own snapshot at every point, the stop):
most keep `rnDurInv`, and `DurAgrees` survives each loop step. Taken:
- **H1:** the loop could not rule out the taken case: it now holds the loop's "not failed" token.
- **H2:** the apply thread could not get its snapshot's term: `walCommitLb` is now a prefix of the
  handed log (a monotone list), not a length.
- **M1:** firing *enter* inside the `Save`'s update would need a later credit: `raftState` is the
  loop's own again (beside its view half), not the invariant's.
- **L1–L3:** `SaveSnap` keeps its I/O premise (the apply thread panics on its error), said so;
  the records' ghost name is the storage's WAL identity (`MinimalEtcdVersion` reopens the WAL
  behind it); `readyGotR` drops the conjunct `deliveredLogLb` implies.
Recorded for R2b-1's proof (docstring of `rnDurTake_stmt`): **M2**, the order is at the view's
handed log, the stop's post at the apply side's `pre ++ A`; equating them needs every sent batch
received (`applyc` is unbuffered; the spsc idiom's spec admits a buffer). **M3**, the apply
thread's token travels with its half of `rnWalTok`. **L4**, `Close` and `rnWalClosed` are R2b-3's.

The draft is ready for R2b-1's proof. Its stages: (1) raft's receive gives `readyGotR`
(`readyRecv_open`, `node.readyRecv.spec`, `readyGot`'s users); (2) the pure laws; (3) the WAL
contract `isRNWalR` in `isRNWal`'s place, `bootstrap`'s contract giving `walRecs` (fresh:
`walFresh`) and the ghost names; (4) the raft loop entering at the `Save`
(`raftNode.start`, `rn_ready_recv`), `notifyc` handing `walCommitLb`; (5) the apply thread's
snapshot; (6) the stop (`raftNode.stop.specStop`, `onStop`).

### The WAL's API, spec-first (2026-11-03, the user's request; approved)

Before R2b-1's proof, the user asked for the WAL's whole API through the spec-first approach
(`notes/decisions.md`, "The WAL's API"). Three review rounds; the axiom review found a third WAL bug
(a restart at a received snapshot names the next file below it; `nonissues/
etcd-wal-restart-file-below-snapshot.md`), fixed on the fork in `323320bb8` (with
`LatestSnapshotEntry` at the highest record); **the pin moves to it once the user pushes
`goose-lean-walsnap`**. The API landed as modules no proof uses yet (`storage/WalRecs.lean`,
`etcdserver/WalApi.lean`, sealed); `InvWal.lean` keeps the durability invariant over it. R2b-1's
stage 3 puts it in place, with the six approved changes to trusted statements.

### R2b-1 stage 2: the pure laws, proved (2026-11-03)

`walFresh_holds`, `walSave_holds`, `walSnapSave_holds`, `walOwnSnap_holds` (`InvWal.lean`), over
three list lemmas (`appendEnts_cons`, `plogTermAt_take_append`, `drop_take_append`) and
`plogTermAt_some_le`: the WAL's records keep holding the durable state across a saved batch with or
without a received snapshot and across the member's own snapshot. The etcd pin moved to the fork's
`323320bb8` (the axiom review's fix; translation unchanged; `restart3` and `putget3` pass).
Next: stage 1 (raft's receive gives `readyGotR`), then stage 3 (the API in place, the six approved
changes).

### R2b-1 stage 1: raft's receive gives its facts before *enter* (2026-11-03)

`readyGot` gains `deliveredLogLb` of the delivered log after the `Ready` and its hard state's
committed fact (`notes/decisions.md`, "Raft's receive gives the delivered log and the committed
hard state before *enter*"). Next: stage 3 (the WAL API in place of `isRNWal`, the six approved
changes) and stage 4 (the raft loop entering at the `Save`), which go together.

### R2b-1 stage 3a-3b: a member's WAL directory fresh at start, `bootstrap` gives the opened WAL (2026-11-03)

The user's choice for change 6: an axiomatized token. `walDirFresh dir` (`storage/WalDir.lean`) and
`walFiles` (`storage/WalRecs.lean`) are axiomatized, timeless only (no exclusivity: read as `True`
every axiom holds, the start axiom's satisfiability argument). Program start gives `walDirFresh`
for the directories `Ds` (`startRights`, `goose_adequacy_start`) under a new environment premise,
`walDirsAbsent e Ds`; `etcd_adequate` and `k8setcd3`'s adequacy pass the members' directories.
`bootstrap`'s contract takes it and gives `walOpened … walFresh` and `walPurgeRight` (in place of
`walOpen` and `walReady`); `NewServer`, `common`'s starters, every example's `Main` and adequacy
theorem and results thread it. The three-member examples (`putget3`, `linkv3p`) take the members'
directories' distinctness as a premise (`config.walDirOf` is opaque: `filepath.Join`). The hub names the WAL through its slots (`wal.bootRes cfg`, `wal.bootOk cfg id cid w`, `WalApi.lean`; the slot convention, `notes/spec-first-plan.md`), not its facts. The trust
base gains `walDirFresh` and `walDirsAbsent` (13 collections). Next: stage 3c with 4.

### R2b-1 stages 3c-6: one landing (2026-11-03, plan)

**Why together.** Putting `isWalStorage` in `isRNWal`'s place (`rnNewStorageOk`, approved change 1)
changes every WAL operation's contract at once: `Save`'s success update needs `WalSaveOk` (the
records tracking raft's log: the durability invariant), the apply thread's `SaveSnap` needs the
records' base term, and `Close` needs the records, the metadata and the purge's right. None of
them can be met from a weaker invariant (`∃ σ, walRecs w σ` does not give `WalSaveOk`). Giving both
contracts during a transition would be unsound (an old `Save` moves the records behind
`walRecs`' back, and `Close` would then give `walFiles` of the wrong records). So stages 3c
(the contract), 4 (the loop's `SaveSnap`/`Save`), 5 (the apply thread's `SaveSnap`) and 6
(`onStop`'s `Close`) land as one, on one branch, built in that order.

**Where the WAL's ghost state lives.**
- `wal.Names` (the draft's `WalNames`) is a field group of the wrapper's names (`RNNames.wal`; the
  slot convention's name-record split), allocated in `NewServer`'s proof from `wal.bootOk` by the
  narrow law `wal.bootOk ⊢ |==> ∃ ν, wal.srvInv … ∗ (the loop's part) ∗ (the stop's part)`, which
  replaces `wal.bootOk_storage`.
- `wal.srvInv` = `rnDurInv ν w` (persistent), in the wrapper's components beside `isWalStorage`.
- The loop's part: its view half and "not failed" token, with the driver's state (`rnDrv`: the
  view's durable state is the driver's `S`), and the metadata and purge right until `onStop`.
- The apply thread's: `walCommitLb` of the log it applied (from `notifyc`'s deposit) and its token
  `ν.app` with its half of the open token (`rnWalTok`, review M3).
- The stop's claim `ν.stop` goes with `srvStopRight` (R2b-2).

**Firing *enter*: at the receive** (the user's choice, 2026-11-03, over the draft's "at the
`Save`", round 3 M1): today's `rn_ready_recv` keeps firing it; the loop's `Save` then moves the
records and the invariant's view from the durable state before the batch to the entered one
(`walSave_holds`, `walSnapSave_holds`, stage 2). Enough for a graceful stop and restart: at every
idle point, where the stop happens, the records hold the node's durable state. Not for a crash
between the receive and the `Save`, which nothing models yet: entering at the `Save` is recorded as
open for crash recovery (it would rewrite `rn_ready_recv` and the middle of both branches of
`raftNode.start`, where the loop would hold no driver).

**The view's half** lives in the loop's token (`rnLoopTokP`), at the durable state of its driver,
which the driver's predicates now name (`rnDrv γ L p S`, `rnBusyN … S`, `rnBusyS … S`: `Advance`
keeps it), with the "not failed" token. Between the receive and the `Save` the view is at the
state before the batch and the busy driver at the entered one; `rn_ready_recv` says how they relate
(`readyDurable`).

**Order of work:** (a) the vocabulary: `RNNames.wal`, the view in the driver's predicates, the
contract in `isRaftNode`, `rnNewStorageOk`; (b) the start: `NewServer` allocates from `wal.bootOk`,
`NodeStart`'s first driver holds the initial view (`RaftState.init`, `walFresh`; `γ.pre = []`);
(c) the loop: receive without *enter*, `SaveSnap`/`Save` with the invariant, both branches of
`raftNode.start`; (d) the apply thread's `SaveSnap`; (e) `onStop`'s `Close`.

**Where it stands (2026-11-03, branch `r2b1-s3c`, built, not landed):** the vocabulary and the
pure halves are done: `RNNames.wal`; the driver predicates name their durable state; `rnDur_alloc`
and `wal.bootOk_start` (NewServer allocates; the names reach `newRaftNode`); the loop's `Save` and
`SaveSnap` as the contract's atomic updates (`rnDur_save_au`, `rnDur_saveSnap_au`, over the pure
`WalSaveStep`/`WalSnapStep`); a received batch is such a step, proved from raft's `ReadyRestFacts`
(`walSaveStep_ready`, `walSnapSteps_ready`), and `rn_ready_recv` hands the steps to the loop
(`rnReadyData`, `rnReadySnap`). Left, as one change: the view's half and "not failed" token in the
loop's token (`rnLoopTokP`, from `NodeStartSpec`); `isWalStorage` in place of `isRNWal`
(`rnNewStorageOk`, `isRaftNode` with `rnDurInv`); the loop's `SaveSnap`/`Save` over the lemmas; the
apply thread's `SaveSnap` (its token `ν.app` with its half of the open token, review M3: `rnWalTok`
takes the wrapper's names, or the apply side's half becomes its own predicate); `onStop`'s `Close`
(the records from `rnDurTake`, with the metadata and purge right the loop keeps from the start).

### R2b-1 stages 3c-6, done (2026-11-03)

The WAL contract is in use: `NewStorage` gives `isWalStorage` (`isRNWal` is gone), the wrapper holds
the durability invariant (`isRaftNode`'s `rnDurInv γ.wal`), allocated in `NewServer` from
`wal.bootOk_start`. Every WAL operation is proved over the contract:
- the loop's `SaveSnap` and `Save` (`rnDur_saveSnap_au`, `rnDur_save_au`; the steps from the
  receive, `rnReadyData`/`rnReadySnap`), its view's half in the loop's token (`rnLoopTokP`'s
  `rnWalView`, the initial view from `NodeStartSpec`);
- the apply thread's own `SaveSnap` (`rnDur_ownSnap_au`), with its token `ν.app` in its WAL share
  (`rnWalTokA`, review M3) and the handed log's bound (`rnWalHanded`, carried by `raftAdvancedC`,
  closed after the loop's `Save`); its chain (`applyAll`, `snapshotIfNeeded`, `snapshot`) takes a
  fresh start's premise `γr.raft.pre = []` (the snapshot's index is the applied log's length),
  which `run` has;
- `onStop`'s `Close` (`rnDur_take`: the records out of the invariant, with the stop's claim, the
  apply token from `stopped`, the loop's view; the metadata and purge right in the loop's share
  `rnWalTokL`).
A failed `Save` is I/O (`¬ storage.walSaveOk`, the user's choice): the invariant has no failed
state. Close's result (`walFiles`) is dropped for now: R2b-3 makes the image from it (`rnWalClosed`,
`srvFiles`). Open: M2 (the order at the view's handed log vs the stop's `pre ++ A`), enter at the
`Save` (crash recovery).

### R2b-3: the image, its plan (2026-11-03)

**A correction first (the user's choice: *enter* at the `Save`).** R2b-1 kept *enter* at the receive
on my claim that the loop stops only at idle points. It also returns on `r.stopped` between the
receive and the `Save` (`raft.go:218`, the read state's send; `raft.go:241`, the hand-off), where the
node had entered the batch and the records did not hold it, so the stop's image was false there
(`notes/decisions.md`, "*Enter* at the WAL `Save`").

The stages:
- **R2b-3a, *enter* after the `Save`** (done, below): the receive keeps raft's wand
  (`rnPendEnter`); the loop fires it once the `Save` returned (`rn_enter`, `rn_enterS`). Before it,
  the loop uses only what the receive gives without *enter*: the committed log, `deliveredLogLb`,
  the hard state's committed fact (`rnHsC`, for `rnRtOk`), and the messages raw (`rnRawMsgs`), sent
  by a leader through raft's `readyLeaderMsgs` (the loop's token keeps `islead` true only at role
  leader: the driver predicates name the role, `rnDrv γ L p S r`).
- **R2b-3b, the raft loop's stop escrow:** `applyc` synchronous (Perennial's `isSspsc`, M2: with
  the producer's token, which the escrow returns, and the apply side's consumer, `sspsc_sync` gives
  sent = received, so the handed log is the apply side's `A`); `done`'s escrow (`rnStopClaim`, an
  invariant: the stop's image or the claim); `node.Stop`'s `nodeVacant` through the wrapper's
  `Stop` clause; `onStop` takes the durable state (`raftState`, the busy driver's or the pending
  *enter*'s) and puts `Close`'s files (`rnWalClosed r id σ := walFiles …`) in the escrow;
  `raftNode.stop.specStop` proved.
- **R2b-3c, the backend's part:** `Cleanup`'s spec (`be.Close` gives the bbolt file's data `D`),
  `srvFiles` defined (the WAL's files and the backend file in `dd`), the image's order at the
  consistent index.
- **R2b-3d, `run`'s shutdown** (R2b-2's `run.specStop`): the image assembled and escrowed in `done`.

### R2b-3a: *enter* after the `Save` (2026-11-03, done)

`InvRaftNode`: `rnPendEnter`, `rnBusyP`/`rnBusySP` (the busy driver before *enter*), `rn_enter`,
`rn_enterS`, `rnRawMsgs` with `rnRawMsgs_sent`/`rnRawMsgs_leader`, `rnHsC` with `rnRtOk_of_hsC`
(replacing `rn_rtOk_busyN`/`busyS`); `rnReadyData`/`rnReadySnap` carry the messages raw and the soft
state's role; `rn_ready_recv` no longer fires *enter* and no longer takes the running token. The
driver predicates name the role; `Advance` keeps it; the loop's token (`rnLoopTokP γ L p b`) ties
`islead` to it. `raftNode.start`'s two branches fire *enter* after the `Save`; at the stop exits
before it the loop holds `raftState` at the state the records hold. No spec outside the wrapper
moved.

### R2b-3b: the raft loop's stop escrow (2026-11-03, done)

- `applyc` is synchronous (Perennial's `isSspsc`, a drop-in for `isSpsc`): the producer's and the
  consumer's tokens together give sent = received (`sspsc_sync`), which settles review M2.
- `RNNames.sc`, the claim (`rnStopClaim γ := token γ.sc`), allocated by `newRaftNode` (in
  `rnBuilt`; `NewServer` drops it until R2b-3d threads it to `run`'s shutdown, `srvStopKeep`).
- `done` announces the escrow `rnDoneEsc γ w := inv rnStopN (rnStopImage γ w ∨ token γ.sc)` at the
  WAL `w` (until then `True`). `onStop` (its spec now takes the durable state, the loop's view at it,
  `applyc`'s producer token and `cum` at its count) allocates it with the image: `nodeVacant` (the
  wrapper's `Stop` clause now gives it, raft's `node.Stop`), `raftState S`, `Close`'s files
  (`rnWalClosedW`: `walFiles` at the member `γ.id`, which `rnWalTokL`'s metadata now names), the
  order of the records' base and commit around the handed log.
- `raftNode.stop.specStop` proved (`wp_proofStop`, over `rn_esc_take`: the claim takes the image,
  the apply side's token at `A` makes the handed log `A`). `spec` stays (its callers don't stop).

### R2b-3c, part 1: the backend's file at its `Close` (2026-11-04)

The user approved the trusted change (scratch candidate 1): bbolt's `Open_kv` records the file
(`dbFile db path`), `DB.Close_kv` takes `ownDB db γ D` and gives `fileHolds path D`. Proved over it:
the backend's names gain `dbf` (the database and its file, `bDBAt`, discarded: `isBackend`,
`batchPhys` name it, so the stop and `Close` agree); `unsafeCommit`/`commit`/`CommitAndStop` give the
stopped batch transaction's database out (`bDBOut`); `run` escrows it on `donec` (`bDoneEsc`, until
then `True`); `Close` keeps half of the close right as its claim (`stop_take`), takes the database
out (`bDoneEsc_take`) and closes it: its post gives the file (`bFile γ path ∗ fileHolds path D`).
`applySnapshot` drops the old backend's file. Trust base: +2 (`dbFile`, `dbFile_persistent`).
Next (part 2): `D` observed (the store's view at the consistent index, as `backend.Snapshot`'s
observation), `New` giving `bFile γ cfg.Path`, `Cleanup`'s spec, `srvFiles` defined.

### R2b-3c, part 2a: what the backend's file holds, its path, the closers' specs (2026-11-04)

Done (`notes/decisions.md`, "The backend's `Close` gives back what its stopped lock held"):
`backend.Close` returns, at the file's data `D`, the stopped batch lock's client resources and ghost
shares (`bStopView`), the material of `backend.Snapshot`'s observation, so `imageAt` of `D` follows
as on the snapshot path; `New`, `OpenBackend` (trusted, approved), `OpenSnapshotBackend` give the
file's path (`bFile`); the lessor's stop right and `lessor.Stop` (trusted, approved);
`authStore.Close` proved. The server keeps `isStopChansE` (the backend's `W`, `Pk` hidden) and drops
the lessor's stop right and the new backend's `bFile`. Trust base: +2 (`lessorStopTok`,
`lessor.Stop.wp_proof`; the `Timeless` instance is not reached).

Left for part 2b: `Cleanup`'s spec (the lessor's stop right and the auth store's `tpAdmin` in
`srvCleanupOwn`; the KV's closer and the backend's `bOpen 1`, `isStopChans` at the server's own `W`,
`Pk` from the apply thread's final state), `srvFiles` defined; then R2b-3d.

### R2b-3c, part 2b: `Cleanup`'s spec, `srvFiles` defined (2026-11-04, done)

`EtcdServer.Cleanup.spec` (proved, linked): from the right to close each thing it closes -- the
lessor's stop right (`lessorStopTok`), the watchable store's closer by the mode (`wsCloserM`), the
auth store's `tpAdmin` (given back), a reader slot of `bemu` with the apply side's half of `s.be` and
quarter of `bemu`'s ghost variable, the backend's stop channels at `W`, `Pk` and the whole open token
`bOpen 1`, the compactor's contract -- it returns what `backend.Close` gives (`bStopView` at the data
`D` the stop's commit left, the file holding `D` or bbolt's close error). No new trust.
`srvFiles dd id σ D` defined (`WalApi.lean`'s plan (3)): `∃ cid, walFiles (walDirOf dd "") id cid σ`
and `fileHolds (backendPathOf dd) D`. `backend.bFile_agree`: `New`'s and `Close`'s paths agree.
`srvCleanupOwn` stays opaque: its sources (the lessor's stop right `NewServer` drops; `tpAdmin`,
the apply thread's in mode `on`, `NewAuthStore`'s otherwise) are R2b-3d's to thread.

**R2b-3d, what is left** (`run.specStop` proved, the image escrowed in `done`):
1. `run`'s loop exits on `s.stop` (its bag at `srvBootApplied`), holding its invariant's resources.
2. The deferred shutdown: `wgMu`/`close(stopping)` (`InvGoAttach`), `cancel`, `sched.Stop` (its
   last job's post: `applyRes` at the log `A` handed to the apply thread), `s.wg.Wait` (the
   goroutines' thread tokens back), `raftNode.stop.specStop` (the raft image at `A`), `Cleanup`
   (the pieces above from the apply thread's resources: `bOpen 1` reassembled from the reader pools
   as `applySnapshot` does, `bOpen_one_pool`; the server's own `W`, `Pk` in place of `isStopChansE`).
3. The image (`srvDiskImage`): the backend's `D` at the consistent index (`imageAt`, from
   `bStopView` by the snapshot path's observation lemmas, `snapObs_window`/`mergedObs`, at the
   apply thread's final state), `σ.b ≤ i ≤ σ.commit` (the raft image's order), `bootLen ≤ i`
   (the stop request's `srvBootApplied`), `confAt`, `v3ConfState D`, the registry's authority,
   `srvFiles` (`walFiles` from the raft image; `fileHolds` at `backendPathOf dd` by `bFile_agree`
   with the backend's `bFile`, which `NewServer` must keep), `pathOwn`.

### R2b-3d: the plan (2026-11-04)

`run.specStop`'s proof: the loop's stop case returns; the deferred shutdown runs; `done` closes with
`srvDiskImage` escrowed. At the loop's exit the invariant holds `rnApplyTok γn A`, the scheduler's
queue and the last job's saved `Post` `Q` with `□ (Q ∗ R -∗ applyResC … A ∗ nodeRunning ½)`:
`sched.Stop` gives `▷ Q`, so the apply thread's resources at `A` come back whole.

The image's clauses against their sources (gaps marked):
- `nodeVacant`, `raftState S`, `StorageHolds S σ`, `σ.b ≤ |pre ++ A| ≤ σ.commit`:
  `raftNode.stop.specStop`'s post (with `rnStopClaim`, `rnApplyTok γn A`, the WAL's apply half).
- `bootLen ≤ i`: the stop request's `srvBootApplied` (the bag's predicate).
- `srvRLogLb ρ.rd.raft A`, `uint.Z i = ai0 + |A|`: `applyResC … A`.
- **Gap 1, the WAL's directory.** `rnWalClosed` gives `walFiles (walDirOf w)`; `srvFiles` wants
  `config.walDirOf dd ""`. `bootstrap`'s `walOpened` knows `walDirOf w = config.walDirOf cfg.DataDir'
  cfg.DedicatedWALDir'` (`WalApi.lean`); to thread, persistent, to `isRaftNode` (the WAL's
  directory) and the scope's `DedicatedWALDir = ""` to the stop right.
- **Gap 2, `imageAt` of `D`.** From `Cleanup`'s `bStopView` (the stopped lock's `W ∗ Pk` and
  halves at `D`) and the apply thread's final state, as the snapshot path's observation does
  (`snapObs_window`, `mergedObs`): the server's own `W`, `Pk` in place of `isStopChansE`.
- **Gap 3, the configuration.** `confStateIs (v3ConfState D) m` with `v3ConfState` opaque
  (R2c's draft, "R2d's to define") is unprovable: define it (`buildConfStateFromV3store`, the
  members bucket's voters and learners) and prove the members bucket of an image at `i` gives the
  membership at `i` (the cluster's apply writes the bucket from the conf changes the log commits).
- Registry authority, `pathOwn (backendPathOf dd)`, `fileHolds (backendPathOf dd) D` (by
  `bFile_agree`): `srvShutdownPre`, `srvSnapRes`, the backend's `bFile` (`NewServer` and the
  snapshot path must keep it).

Stages: (1) gap 1; (2) `Cleanup`'s preconditions from `applyResC` and `NewServer`'s kept pieces
(`srvCleanupOwn` defined, `srvStopKeep`); (3) gap 2, the image's backend part; (4) gap 3; (5) the
shutdown's WP and `run.specStop` (then `spec` replaced, R2b-2 review F4).

### R2b-3d: stage 1 done; gap 4, the readers' open shares (2026-11-04)

Stage 1 landed (`e072cd1e4c`): `srvStopKeep` (the raft loop's stop claim, the registry's
authority, the lessor's stop right, the WAL's directory) from `NewServer`; `bootOk` and
`srvSnapRes` keep the backend's `bFile`.

**Gap 4 (blocks stage 2).** `backend.Close` takes the clients' whole open token `bOpen γ 1`, and
must: a reader's share (`rdOpen`) is its proof the backend is not stopped, so the close collects all
of them. At the server's stop they are not collectable:
- the constructors' half: the apply thread's `srvOpenQ` (`srvSnapRes`), the auth realization's
  quarter on;
- the pool's `rdPoolN + authRdN` shares: in the readers' thread pool (`bkRPool`,
  `threadPool.isThreadPool rdPoolNs`, a plain `inv` of Perennial's `ThreadPool`), copies lent to
  the request path's goroutines against their thread tokens; an `inv` never gives them back;
- the stock's `rdStockN`: the store's readers (`mvcc.storeReader`, `bkRTx`), of which
  `watchableStore.Close` returns only its loops' `wsLoopN`.

The Go code agrees that this is a real condition: `Cleanup` closes the backend whatever the request
path is doing (etcd's `embed.Close` stops the gRPC servers before `Server.Stop`, `stopServers` under a
`ReqTimeout` deadline, `server/embed/etcd.go`; `EtcdServer.Stop` alone does not), and a read on a closed bbolt transaction fails. Options:
1. **A cancelable reader pool and a quiescent request path** (recommended): a general Perennial
   change, `ThreadPool` with a cancelable invariant whose cancel, with every loan back
   (`ownTokAuth γ 0`), returns the copies; the stop's caller gives back the request path's loans
   (its goroutines joined, as `embed` does), and the stores' readers come back from their closes.
   The exported restart result gains the premise that the members' request paths stopped first.
2. **Readers that tolerate a stopped backend**: drop the reader's open share; a read gets either
   its view or a failure after `stopQ`. This needs a trust-boundary spec of bbolt's reads on a
   closed database, and the request path's specs gain a failure case.
3. **Restrict the restart scope**: no request in flight is modeled at the stop, so the pool is
   built cancelable from the start and never lent past the stop. This is option 1 without the
   join, and it is valid only for the examples whose clients finish first.

Stages 3 (gap 2) and 4 (gap 3) do not depend on it and go first.

**Gap 4, decided (the user, 2026-11-04): option 1**, a cancelable reader pool and a quiescent
request path. Steps:
- (4a) Perennial, a general change on a branch off its `lean`: `ThreadPool`'s cancelable form
  (`isThreadPoolC N γ c R`, a `cinv`), with `cancel` giving back the `m` copies left and the count
  of loans out (`ownTokAuth γ b`), and a law that the auth at `b` with `b` loans `ownThreadLoan γ`
  gives `b` more copies. Record it in `notes/perennial-changes.md`; land it by Perennial's workflow
  and bump the pin.
- (4b) `bkRPool` over it, its cancel token kept with the constructors' half (`srvSnapRes`).
- (4c) The stop's caller returns the request path's loans, and the stores' readers come back from
  their closes. The exported restart result gains the premise that the members' request paths
  stopped first.

### R2b-3d gap 3: the configuration a restart reads (2026-11-04, design)

`bootstrap` builds raft's `ConfState` from the `members` bucket (`buildConfStateFromV3store`):
voters are the members whose JSON says `IsLearner` false, learners the rest, in Go's map order
(random). The image claims `confStateIs (v3ConfState D) m` with `confAt γ.cl i m`, and the server's
cluster is static: `srv_confAt_simple` gives `m = Membership.simple γ.raft.cfg`.

**Definition, no new trust.** `v3ConfState` (opaque) becomes the relation `v3ConfStateIs D cs`: some
members `ms` whose entries are exactly the `members` bucket's (`memberKey mm.id ↦ memberEnc mm`,
the shape `membersDecode` already states), `cs.Voters'` a permutation of the non-learners' ids,
`cs.Learners'` of the learners', no joint or auto-leave state. `bootOkR` gives `∃ cs, ⌜v3ConfStateIs
D cs⌝ ∗ memStorRestarted … cs`; the image gives `⌜∀ cs, v3ConfStateIs D cs → confStateIs cs m⌝`.
The relation, unlike the function, admits Go's random order.

**The proof.** By induction on the log, as `membersDecode_restModel`, the `members` bucket of
`restModel 0 boot L` is `{memberKey id ↦ memberEnc (ccMemberAt cc)}` over the boot log's applied
`AddNode`s: later ones re-add a member, which `ccValidOn` refuses, and a static cluster has no
other changes (`ccBootOk`). With `bootLen ≤ i`, that is all of `cfg` (`srvBootLogOk`).

**The hole: learners.** Nothing says a boot member is a voter: `ccMemberOf ctx` is opaque, and
`ccContextOf`'s Bool is `IsPromote`, not `IsLearner`. A boot context whose JSON says `IsLearner:
true` would restart raft with a learner where `confAt` says voter, so the image needs the fact.
etcd's `--initial-cluster` members are voters (`NewClusterFromURLsMap`). The fact goes in as a
premise on the boot log's contexts: `∀ cc of the boot log, (ccMemberAt cc).isLearner = false`, in
`srvBootLogOk` (or the examples' `BootLog`), which the examples' configurations meet. This changes a
premise of exported results, so it is the user's to approve.

**Gap 3, done (2026-11-04).** The pure part is `RestConf.lean`'s `restModel_confState`: given the
image's `members` bucket equal to the rest model's at `boot ++ R`, every `cs` with `v3ConfStateIs
D cs` gives `confStateIs cs (Membership.simple cfg)`. Stage 5 discharges its premises:
`srvBootLogOk`, distinct peers, `bootURLsOk` (`srvClusterOk`), the boot entries' and the log's conf
changes `ccApplyOk` (`srv_committed_ccBoot`; empty V2 entries excluded by
`committed_emptyV2_joint`), and the bucket from `imageAt`'s `bkRestAtL`. Trust added: three
reviewed axioms (`notes/axiom-review/members-decode.md`).

### R2b-3d stage 3: the image's backend part (2026-11-04, plan)

`Cleanup` returns `bStopView γ P W Pk D` at the stop channels' `W`/`Pk`, but the server keeps the
channels as `isStopChansE` (some `W`, `Pk`), so nothing is known of `D`. Steps:
1. **Sharpen.** The server's channels are at its own resources, the same at construction and at
   every install: `W = mvcc.lateWD d` and `Pk = batchLockInv γA (metaTM d.γB d.P)`, at the apply
   thread's current names `γA` (`γ.withPh (futPhys π0 γB)` after an install). `srvSnapRes s E`
   becomes `srvSnapRes s E γA`, with `isStopChans` there; `srvSnapOwn` and `applyResC` pass `B.γ`;
   the snapshot path's posts give it at the new names.
2. **Observe.** Factor out the core of the snapshot window
   (`SnapSendBranch.lean`, the proof that feeds `backend.Snapshot`'s `Q`): from the apply thread's
   resources at `A` and the lock's pieces (`W`, `Pk`, `viewAt`, `pvHalf`, `hkOwn`, `rbOwn`,
   `ckHalf` at `D`) to `⌜mergedObsM … D⌝`. The stop applies it to `bStopView`'s pieces, the window
   to the snapshot's.
3. **Image.** `merged_imageC`'s pure part, from `mergedObsM` to `imageAt` (stage 5 assembles the
   rest).

**Stage 3, progress (2026-11-04).** Step 1 landed (`6fbf7eed05`): `srvStopChans`. Step 2a: the
stop's commit leaves a reader's bound of the compaction keys' flag at its data (`bStopG`'s and
`bStopView`'s `∃ R, fkRd γ P (C, R)`, from `unsafeCommit`'s stop branch, `fkHalf_rd`), what
`txn.kvWriter_noCmp` needs for `fkAbsD D` in a store that does not compact.

**Open: the stored consistent index at the stop.** `imageAt` needs `D`'s `consistent_index` key to
be the applied index `i`. The snapshot window gets it by freezing the protocol at a commit it
requests (`storeReq_freeze` through `kv.Commit`, `commit_freeze_au`, `freezeY`: the stored index is
`ciEff γ s.k`). The stop has no such request: `backend.Close`'s stop commit runs the server's hook
on its own, and outside the window the protocol knows only `mi ≤ s.k` (`consInvAt`). In Go the
stop commit's hook stores the current index, since the apply thread is idle. So the stop needs a
way to record that its commit came after the last apply. Candidates:
- (a) A freeze request for the backend's stop commit: `Close`'s caller deposits the apply thread's
  state; the stop commit's hook runs `commit_freeze_au`; afterwards the frozen protocol
  (`consFrozen`) gives `mi = ciEff γ s.k`. This threads a request through `CommitAndStop` to
  `OnPreCommitUnsafe`.
- (b) The protocol remembers the last commit's index: a commit's hook leaves a persistent
  lower bound of what it stored (`mi ≥ ` the index at the commit), and `Close`'s post says a commit
  ran after `Close` was called; the apply thread, idle at `s`, then knows `mi = s.k`.
To be designed next.
- **Chosen: (a), over the backend's own commit requests.** `commitReq γ P Pk b X Y` (`InvBackend`)
  already lets a commit take `X` and give `Y` through the hooks (the snapshot window's
  `commitReq_freeze`). `backend.Close` gains a request: its caller gives `commitReq … X Y ∗ X` (the
  stop's: `X = applyThread γ s`, `Y = freezeY γ s`, `commitReq_freeze`). The stop invariant passes
  it to `run`, whose `CommitAndStop` commits with it, and the done escrow (`bDoneEsc`) returns `Y`
  with `bStopView`. `Close`'s callers without a request pass `commitReq_true`. Step 2b.
- **Refinement (same day).** Step 2a landed (`a2887278cb`). The request can't simply be fixed in
  the stop channels: `New` allocates `stopInv`/`bDoneEsc`, but `X = applyThread γ s` is known only at
  `Close`. Two ways for step 2b:
  - **(a1) per call.** `stopInv`'s second state holds `∃ X Y, commitReq … X Y ∗ X ∗ savedProp γY Y`;
    `run` commits with the request and escrows `Y` in `bDoneEsc` under the same saved name; `Close`
    reads it back. This needs a saved-proposition ghost.
  - **(a2) armed in the apply protocol.** The idle apply thread arms a freeze in `consInv`
    (depositing its state), and every hook commit (`commit_save_au`) that finds it armed freezes,
    while `Pk`'s `metaTM` records that it did. After `Close` the apply thread finds the protocol
    frozen at `ciEff γ s.k`. This changes the hook's commit AU and touches every commit.
  Leaning to (a1), local to the backend's stop protocol.

**Step 2b done (2026-11-04), option (a1).** `BNames.rq` (a saved proposition); `stopReq`;
`stopInv γ P Pk b sc γsc` (both halves at `True` before `Close`, the request deposited after);
`CommitAndStop`, `Close` and `Cleanup` take `X ∗ commitReq … X Y` and give `Y`; `run` carries
the request to the stop's commit and its result to `donec`'s escrow. Callers with no request
(the snapshot walk's old backend, `bootstrappedBackend.Close`) pass `commitReq_true`. The server's
shutdown passes `commitReq_freeze`'s `applyThread γ s ⇒ freezeY γ s` (stage 5), so after
`Cleanup` the frozen protocol pins the stored index (`snapObs_window`'s `ciObs`).

**Stage 3 done (2026-11-04).** `SnapSendBranch.mergedObsM_of_obs` (the window's pure block,
shared) and `StopImage.stop_mergedObs`. The latter turns the frozen protocol, the apply thread's
halves of the tracked buckets, the KV's writer and compaction right, and `Close`'s `bStopView` at
the server's resources into `⌜mergedObsM … D⌝`. Stage 5 turns that into the image (as
`merged_imageC` does for the snapshot: `kvAppliedM`, `isServerM`, the KV log's receipt).

### R2b-3d gap 4, corrected (2026-11-04)

The first analysis was wrong about where the open token's shares are. A reader slot of the
backend's thread pool (`rdTok`: `readTx.mu`'s slot, `txMu`'s, a budget token) carries **no** open
share. The pool's shares (`bOpen rdOpen`, `rdPoolN + authRdN` of them) sit beside the pool in
`bkRPool`, which the apply thread holds, so nothing locks them in an invariant. The snapshot path
already closes an old backend with the whole token (`SnapApplyWalk`, the old backend's
`Close`). It collects:
- the constructors' half;
- `bkRPool`'s shares;
- the old store's reader stock (`nReaders - 1` `storeRT`s, which `store.Restore` returns:
  `snap_oldReaders`), and a monitor's reader.

So the cancelable thread pool (Perennial `c0a2fdd46`, landed) is not what the stop needs, and step
4b as planned is dropped. (The change is general and stays.) What the stop needs is the **store's
reader stock**. `store.Restore` returns it because it takes the store's write lock, so no
transaction holds a reader. Go's `store.Close` (through `watchableStore.Close` in `Cleanup`) takes
no lock, and its spec returns only the watch loops' readers. A request-path transaction still
running holds a reader, and with it a share of the backend's open token. So the user's choice
stands, reinterpreted: the request path stops before the server, and the stop collects the store's
readers.
- **4b′.** A store-level law: with every reader ticket back (none in flight), the store's
  invariant gives up the whole stock, as `Restore`'s write lock does.
- **4c′.** Where the request path's readers are at the stop, and the premise that returns them.
  To be designed after looking at how the request path borrows its readers.

### R2b-3d gap 4: the store's readers at the stop, a census (2026-11-05)

`backend.Close` needs every share of the open token. `NewServer`'s own error path (R-D1, the
deferred `b.Close()` after `kv.Close()`) is the template: it collects every store reader and
retires them at once (`storeReaders_retire`, `storeRTs_shares`), then adds `bkRPool`'s shares and
the constructors' half (`bOpen_one_pool`). On the success path, `NewStore`'s
`rdStockN − nJobRd` readers go:
| readers | where | at the stop |
|---|---|---|
| 64 (request goroutines, `Hsrs`) | `srvServeBuilt` → `memberUp`'s serving stocks (`kvServeStocks`) | the caller: the stopped member of `restart3` never served gRPC (only member 1 serves before the restart), so they are unused |
| 64 (watch run slots, `Hwrx`) | `srvWatchReaders` in `memberUp` | the caller, unused likewise |
| 1 (compactor, `HwrC`) | `srvCompactR` (`NewServer.lean:1942-1974`) | with the compactor; `restart3` runs none (to check) |
| 1 retired (storage version monitor, `HrtSV`) | `srvWTStock` (`:1809-1817`) | to trace (the server's goroutines, `s.wg.Wait`) |
| 1 retired (apply thread, `HrtA`) | `apply.kvOwn`'s `writerOwn` | `applyResC` |
| 2 (watchable store's loops) | the watchable store | `watchableStore.Close`'s post (`Cleanup`) |
| the compaction job's resource | the store | `compactJobResM`, `watchableStore.Close`'s post |
| **the rest, about 805 million (`Hwrds`)** | **dropped** (`NewServer.lean:2380`: one taken, the rest `-`) | **lost: must be kept** |
So the stop needs no new store law: `storeReaders_retire` with every reader is it (4b′ dropped).
4c′ is plumbing:
1. `NewServer` keeps the remainder (`srvStopKeep` gains the readers; a stronger post).
2. The stop's caller returns the member's unused serving stocks (`memberUp`'s request and watch
   readers). This is the "request path stopped first" premise, met in `restart3` because the
   member never served.
3. The compactor's and the monitor's readers are traced.
4. The shutdown (stage 5) assembles the token as R-D1 does.
Auth off only: `restart3`'s mode. Auth on adds `authAbandonM`, as R-D1 does.
- **Step 1 done (2026-11-05):** `NewServer` keeps the remainder (`srvKeepRdN γst` store readers in
  `srvStopKeep s γn wdir st γst`). `srvShutdownPre` and `run.specStop` take the store, and
  `memberBuilt`'s `K` receives the environment.
- **The compactor's reader (2026-11-05):** `restart3`'s members run none. With no compactor its
  reader was dropped too. `srvStopKeep` now keeps it when the compactor field is nil (a disjunction
  on `cp`); with a compactor, the compactor's run keeps it. Census closed for `restart3`: the stop
  collects `srvStopKeep`'s readers, the compactor's (nil), the apply thread's (`apply.kvOwn`,
  `writerOwn`), the monitor's retired one (`srvWTPool`), the loops' (`watchableStore.Close`) and
  the caller's unused serving stocks (`memberUp`).

### R2b-3d stage 5: the shutdown and `run.specStop` (2026-11-05, plan)

`run`'s deferred function (`server.go`):
```
s.wgMu.Lock(); close(s.stopping); s.wgMu.Unlock(); s.cancel(); sched.Stop(); s.wg.Wait()
s.r.stop(); s.Cleanup(); close(s.done)
```
Each step and its source:
| step | spec | gives |
|---|---|---|
| `wgMu.Lock`, `close(stopping)` | `wgMuP`'s protocol (`GoAttach`) | no goroutine attached after |
| `cancel()` | `context`'s | — |
| `sched.Stop()` | `schedule.fifo.Stop.spec` | the last job's saved post: `applyResC … A ∗ nodeRunning ½` |
| `s.wg.Wait()` | the server's wait group | the attached goroutines' tokens |
| `s.r.stop()` | `raftNode.stop.specStop` | `nodeVacant`, `raftState S`, `StorageHolds S σ`, the WAL's closed files |
| `Cleanup()` | `EtcdServer.Cleanup.spec` with `commitReq_freeze`'s request | `freezeY`, `bStopView` at `D`, `fileHolds path D`, `bFile` |
| `close(done)` | `srvDoneInv` | the image escrowed |
The image (`srvDiskImage`), clause by clause:
- raft's part from `r.stop`;
- the backend's from `StopImage.stop_mergedObs`, then the pure part of `merged_imageC` (`mergedObsM` → `imageAt`);
- the configuration from `RestConf.restModel_confState` (premises from `srvRaftLogInv`, `srvBootLogOk`, `srvClusterOk`'s `bootURLsOk`, `srv_committed_ccBoot`; empty V2 entries excluded);
- the files from `Cleanup`'s and `r.stop`'s posts (`srvFiles`, `bFile_agree`);
- the registry's authority from `srvStopKeep`;
- `bootLen ≤ i` from the stop request's `srvBootApplied`.
`Cleanup`'s whole open token is gap 4's census: `srvStopKeep`'s readers, the apply thread's, the loops' and the caller's unused serving stocks. So `run.specStop` (or `HardStop`'s caller) also takes `memberUp`'s unused stocks.

Steps: (5a) the image's pure assembly lemma (`imageAt`, the configuration, the index bounds), from the observations, in a module of its own; (5b) `Cleanup`'s preconditions from `applyResC`, `srvSnapRes`, `srvStopKeep` and the stocks (the open token by `bOpen_one_pool`, as R-D1); (5c) the deferred function's WP; (5d) `run.specStop` (a variant of `run.wp_proof`, the stop clause taken).

**Stage 5a done (2026-11-05, `3e8f0abc0c`):** `StopImage.merged_imageAt`, `imageAt` from
`mergedObs` (the pure part of `merged_image`).

**Stage 5b, the design.** `Cleanup`'s preconditions at the stop:
- from `srvStopKeep`: the lessor's stop right, and the compactor field (nil in `restart3`;
  `compactorOk nil` is its left case);
- from `applyResC`: the KV's closer (`srvSnapRes`'s `srvKVCloserW`; off, `wsCloser`, which is
  `wsCloserM`'s off case), `bemu`'s reader slot, the apply side's half of `s.be` and quarter of
  `γbe` (`srvApplyKVCore`'s `srvBeOwn`), and the stop channels at the server's resources
  (`srvStopChans`);
- the request: `commitReq_freeze` over the idle apply thread (`applyThread γ st`, from
  `applyResC`; its premises are `isServer`'s);
- `bOpen 1`, by gap 4's census;
- two pieces to add:
  1. `srvShutdownPre` takes the caller's unused serving stocks: `memberUp`'s 64 request and 64 watch
     store readers, routed through the drafts.
  2. `srvCleanupOwn` is defined: the auth store's `tpAdmin`, which `NewServer` keeps (off mode,
     `restart3`).

**Stage 5b, the two pieces done (2026-11-05):** (1) `srvShutdownPre` takes 128 store readers (the
unused request and watch stocks; the watch readers through `watchReader_storeReader`). (2) With
auth off nothing held `tpAdmin` or the store's invariant (the off store is `NewAuthStore`'s axiom's),
so the user approved a persistent `Close` contract in the axiom's post (`authCloseOk`, reviewed:
`notes/axiom-review/auth-close.md`). `Cleanup` takes a closer `authCloser stl K ∗ K`;
`srvCleanupOwn s` is the `authStore` field with `authCloseOk`, which `NewServer` posts with auth off.
`notes/decisions.md`, "The auth store's `Close` at the stop". Left of 5b: assembling `Cleanup`'s
whole precondition at the stop (with `bOpen 1` from the census), done inside 5c's proof.

**Stage 5c, first part (2026-11-05): two gaps closed.** (1) `raftNode.stop` takes the environment's
`ST`, which was `False` for the server: now `srvTrStopK γk`, rebuilt at the stop from `srvApRes`'s
live transport and `NewServer`'s `srvTrKeyOf` (`srvApRes_trStop`, `srvTrStopK_of`). `run.specStop`
must add `⌜Er.ST = srvTrStopK γk⌝ ∗ srvTrKeyOf s γk` (5d). (2) `Cleanup` takes, in place of `bOpen 1`,
an update from `kv.Close`'s returns (the loops' `wsLoopN` readers, `compactJobResM`) to `bOpen 1`.
`GoAttach`'s side: `goAttach_close` (the writer under `wgMu`: flag open, closed, "no waiters" out),
`wp_goAttach_Wait`. Left of 5c:
- the census update for `Cleanup` (off mode): `bOpen ½` (`srvSnapRes`), the pool's shares
  (`srvBeOwn`'s `bkRPool`), and `rdStockN` shares from `storeRTs_shares`: retire (one `£`,
  `writerFrag` from `kvOwn`'s `kvWriter`, `retiredAt (2 + nJobRd)` from `writerOwn`) the readers:
  `srvKeepRdN` and the compactor's (`srvStopKeep`), 128 (`srvShutdownPre`), the apply thread's own
  (`kvOwn`), the loops' 2 (`kv.Close`); with the retired ones: `writerOwn`'s `storeRT` and the
  monitor's, in `srvWTPool`'s invariant (`bkRTx`, swapped out for a fraction of `dghostVar E.γbe`:
  `Cleanup` passes its quarter through untouched, so a smaller fraction will do there);
- the stop commit's request (`commitReq_freeze`) and the image (`srvDiskImage`) for `close(done)`
  (allocating `srvDoneInv`'s invariant with the image in it);
- the deferred function's WP in `run.specStop`'s proof (5d).

**Stage 5, the stop slot (2026-11-05, hub request H1, accepted).** The stop's pieces that were inline
in `NewServer.specG`'s post (`srvTrKeyOf`, `srvStopKeep`, `srvCleanupOwn`'s mode clause) are one
sealed slot, `srvStop.keep s cfg E γrn γk` (`StopApi.lean`, modelled on `WalApi.lean`). Its narrow
eliminations each give one consumer what it takes:
- `raft_stop`: `raftNode.stop`'s `ST`;
- `cleanup_pieces`: `Cleanup`'s lessor and auth closer;
- `census_readers`: the census's readers;
- `image_inputs`: the image's registry and WAL directory.

`memberBuilt`'s `K` gains the key's name. `srvShutdownPre` moved to `StopApi`.

**Stage 5c/5d done (2026-11-05; `notes/decisions.md`, "The stop's slot, the shutdown, and the monitor's read token").** `run`'s proof is one proof over a stop flag,
`run.wp_proofG stp`, with `run.spec` at `false` and `run.specStop` at `true`.
The deferred shutdown is proved step by step:
- `wgMu.Lock`, `goAttach_close`, `close(stopping)` (`wp_stop_chan_close_at`, the closer's flag at
  `wgMuP`'s names), `Unlock`;
- `cancel()`;
- `sched.Stop()`, then saved-proposition agreement for the last job's `Q`, which gives `applyResC … A`
  and `nodeRunning ½`;
- `wg.Wait()`;
- `r.stop()`, with `srvApRes`'s transport and the slot's key giving `Er.ST`, and `stop_split`;
- `Cleanup()` (`StopShutdown.stopCleanupImage.spec`; see the list below);
- `inv_alloc` of `srvDoneInv` with the image, then `close(done)`.

What `Cleanup()` does, with its stop commit's request and the image:
- the census, as `NewServer`'s R-D1 path: the slot's readers and the nil compactor's, the 128 unused
  serving readers, the apply thread's, and the loops' from `wsCloseRes`, retired; then the retired
  `writerOwn` reader and the monitor's; the stock, the pool and the constructors' half give `bOpen 1`;
- `commitReq_freeze`;
- `stop_mergedObsP` (`stop_mergedObs` at the writer's pin, since the census consumed `writerFrag`);
- `merged_imageAt`, `restModel_confState`, `srvFiles`.

New scope premises on `run.specStop` (a draft): no compactor, auth off , no compaction mode and
the boot log's `Nodup`/`srvBootLogOk`.

**The storage-version monitor's read token.** The census needs the monitor's read token, which
sits in `srvWTPool`'s invariant. Its checked-out case (a monitor session) could not be ruled out:
the monitor's trusted contract posted `True`, and `GoAttach`'s `Done` returned nothing. The user
approved widening the monitor's contract, with the smaller design that followed:
- the pool's names become a record `W = ⟨cnt, reg⟩`, where `reg` is a set-once register of `γg.run`
  that `start` records;
- `GoAttach` hands the goroutine's receipt `goRunning γ` to `f`;
- the monitor's session deposits that receipt in the pool's checked-out case and takes it back before
  it returns;
- `wg.Wait()` gives the persistent `goWaited γ`, which contradicts any receipt.

This is done (`stop_monitorRT` proved; `goWaited` is an exclusive half, and `Cleanup` takes any
fraction of `γbe`). The widened contract survives the `axiom` skill's attack. F4 (`run.spec`
replaced by `run.specStop`) is deferred until the scope premises are lifted or carried (R2d).

### R2c Scope (2026-11-05, for the user)

Session etcd-grove-83, branch `r2c-scope` (off `lean` `5a00eca26c`, after hub step 7's Freeze, tag
`hub-step7-frozen`). Design only: no Lean edited, nothing built. **A hard stop: the user's Scope.** The
questions (Q1-Q9) and the agent's pending decisions (D1-D3) are in the worktree's `questions.md`.
Line numbers are at `5a00eca26c`. Sizes are estimates (marked "est.").

**The brief** (the coordinator's): R2c verifies
1. `run.specStop`'s scope premises lifted, or carried with a reason;
2. the boot log's facts (`Nodup`, `srvBootLogOk`) moved from premises into `run`'s context;
3. a restarted member's `run` (its start index after a restart), the KV invariant at restart with
   `kvInv`'s new `log0` premise discharged by `txn.soleWriter_small'`;
4. `BuildServer.specStop` and `BuildServer.specRestart` proved.

**The recommendation, in one paragraph.** Split. R2c closes the **stop chain** for a first start:
items 1, 2, `BuildServer.specStop` (item 4's first half) and F4 (one spec of `run`). It adds no
axiom. Items 3 and `specRestart` (item 4's second half) are this plan's L5 (`NewServer` over a
restart boot) plus the raft wrapper's `RestartNode` path: the old stage list's R2d. Reading the code
for this Scope found that they are larger than "the start index is not 0" (findings F-a to F-c).
They go to R2d with its own Scope, and the closed theorem A4 with them.

#### What reading the code found

- **F-a. A restarted `run` starts at the WAL snapshot's index, not the backend's.** `run` sets
  `appliedi: sn.Metadata.GetIndex()` from raft's storage snapshot (`server.go:810-813`). After a
  restart that is the WAL snapshot's index `σ.b`. The consistent index `c₀` is the backend's `i`,
  with `σ.b ≤ i` (`srvDiskImage`, `InvRestart.lean:129`).
  - `isServerRun`'s `%HEr` (`InvRun.lean:53-54`) has `c₀ ≤ ai₀ ∧ γn.pre = [] ∧ ai₀ = 0`. At a
    restart the first conjunct is reversed: `ai₀ = σ.b ≤ i = c₀`.
  - The entries in `(σ.b, i]` are applied again with `shouldApplyV3 = ApplyV2storeOnly`
    (`server.go:1924-1942`), which skips their KV writes.
  - So item 3 is not "`ai₀ ≠ 0`". It is "`ai₀ = σ.b` (which may be 0), `c₀ = i ≥ bootLen`, and a
    replay window".
- **F-b. The raft node's restart point and the server's raft names differ.**
  - `srvRaftLogInv` fixes the server's raft names at `pre = []`, `ai0 = 0` (`SrvRaftLog.lean:740`).
    A restart keeps them: `restartNames` keeps `ρ.rd.raft`, `InvRestart.lean:501`.
  - `run`'s proof equates the raft node's `γn.pre` with them (`hpr : C.γr.raft.pre = γn.pre`,
    `EtcdServer__run.lean:313`, and 22 places in that file).
  - `RestartNode` hands the `Ready` loop the committed log from `max σ.b Applied`, so the restarted
    node's `pre` is the first `σ.b` entries.
  - So the restart generalizes `run`'s relation between the two: R2d.
- **F-c. `kvInv` belongs to the cluster, not to a member.**
  - It is allocated once (`srvClusterBoot_alloc`, `NewServerAlloc.lean:154-170`) at the cluster's
    KV names. `NewServer.specG` takes it as a premise (`"#Hkvinv"`, `NewServer.lean:280`).
  - `kvInv_congr` (`NewServerAlloc.lean:70`) moves it to any names that agree on 11 fields: `st`,
    `c0`, `ch0`, `log0`, `ids.issued`, `ids.wn`, `cmp`, `rlog`, `cret`, `lm` and `kvPfx`.
  - `restartNames` agrees on 6 of them (`st`, `c0`, the KV model, `issued`, `pfx`).
  - So a restart need not allocate a `kvInv`. It reuses the cluster's once `restartNames` covers
    `kvInv_congr`'s fields. Then the revroom-b requirement (a restart-time allocation's `log0` bound
    from `soleWriter_small'`) does not arise. The restarted store's own log bound still comes from
    the sole writer (`soleWriter_small'`), as the snapshot path's does (`SnapSendBranch.lean:357`).
    That is Q8, for R2d.
- **F-d. The compactor is stopped after the backend closes.** `Cleanup` runs `be.Close()` and only
  then `compactor.Stop()` (`server.go:960-967`).
  - A running compactor holds one of the store's readers (the census), and in the model every
    store reader holds a share of the backend's open token.
  - So "no compactor" cannot be lifted without one of: a compactor reader that holds no open
    share (the compactor's `Rev()` reads only the in-memory revision); a Go reorder (a fork
    change); or a third disjunct. Go itself is fine: after the close the compactor's `Compact`
    goes through raft and fails.
- **F-e. `run.specStop` takes the 128 unused serving readers when `run` starts**
  (`srvShutdownPre`, `StopApi.lean:185`). At `Start` they are `memberUp`'s serving stocks.
  `restart3`'s stopped member never serves, so it can give them. A serving member cannot, so F4
  (every `run` stoppable) needs them at the stop instead.
- **F-f. `BuildServer.specStop` cannot be proved from `newServer.spec` as frozen.**
  - `newServer.spec`'s post is `memberBuilt … ∗ leaseTTLRowR` (`newServer.lean:87`), with
    `memberBuilt`'s `K` at its default `True`. That drops the stop slot `NewServer` posts
    (`srvStop.keep`, `NewServer.lean:361`).
  - Nothing gives `srvDataDir` today (grep: its only producers are drafts).
  - `BuildServer` also has three specs (`spec`, `specStop`, `specRestart`) for one function, against
    "one spec per function".
- **F-g. The draft hypotheses the restart example rests on:**
  - `Start_builtS_spec` and `Start_builtR_spec` (`StartStop.lean:37,53`);
  - `BuildServer.specStop`/`specRestart` (`startMember.lean:42,139`);
  - `http.ListenerClose_spec` (`ListenerClose.lean:58`).

  `HardStop.wp_proof` and `run.wp_proofStop` are proved. `restart3` has no `Link.lean` and no
  closed theorem.

#### Item by item

**Item 1: the scope premises** (`run.specStop`'s pure conjunct, `EtcdServer__run.lean:90-91`;
consumed by `stopCleanupImage.spec`, `StopShutdown.lean:404-414`).

| premise | why it is there | to lift it | recommendation |
|---|---|---|---|
| `v.compactor = nil` | a running compactor holds a store reader at `be.Close` (F-d) | a share-free reader of the compactor (the compactor's slot, K-plan specs), or a fork reorder (a hard stop) | **carry** (Q2) |
| `E.authOn = false` | `Cleanup`'s on-mode closer is the apply thread's `tpAdmin` (`authApplyRes`), not threaded; the census adds `authAbandonM` (as R-D1); the image's auth-on chain (`notes/STATUS.md`'s gap H, "a restart's `imageAt` cannot be met after `AuthEnable`", open Q7) | medium for the stop (no trust); the image's gap H unknown (guess: large) | **carry**: no auth-on restart example; a widening of its own |
| `E.cmp = false` | `apply.cmpOwn` is both what `kv.Close` takes (`wsCloserR`) and what the image's observation reads (`apply.cmpObs`); and RESTART-RCPT (the image lacks the compaction-mode receipt, `InvRestart.lean:124-128`) | medium, plus RESTART-RCPT (`notes/image-cmp-plan.md`) | **carry** |
| `Er.ST = srvTrStopK γk` | a fact of the construction (`srvErM`'s), not a scope restriction | moves into `isServerRun`'s `%HEr` (D1) | **move** |

**How the carried premises are carried (Q2, recommended (b)): in the stop request, not in `run`'s
precondition.**
- A new persistent, sealed fact `srvStop.scope s` (`StopApi.lean`) says the server can be stopped:
  no compactor, auth off, no compaction mode, and no dedicated WAL directory (`srvDataDir`'s
  condition, which the image needs).
- `NewServer` gives it inside the slot when its configuration is in scope (a law
  `srvStop.scope_of`, from `v3compactor.bootCfg` off, `on = false`, `cmp = false`).
- The stop channel's predicate becomes `srvStopReq s ρ := srvBootApplied ρ ∗ srvStop.scope s ∗
  128 store readers` (F-e's readers too).
- `run`'s stop branch gets the scope from the request it received.
- `HardStop`'s caller proves it from its member: in `restart3`, the member was built in scope, and
  `memberUp`'s unused stocks give the readers.
- `run`'s precondition then has no scope premise, which is what F4 needs.

**Item 2: the boot log's facts** (`run.specStop`'s `ρ.rd.raft.raft.vs.Nodup ∧ srvBootLogOk vs boot`,
consumed by `stop_imageConf`, `StopShutdown.lean:322`). Recommended (Q3): in `srvRaftLogInv`, the
cluster's invariant, which `run` already has through `isServer`.
- Its last conjunct `∃ ps, ps ≠ [] ∧ srvBootLogOk ps γ.raft.boot` becomes `γ.raft.vs ≠ [] ∧
  γ.raft.vs.Nodup ∧ srvBootLogOk γ.raft.vs γ.raft.boot`.
- The conjunct count does not change, so the `-` patterns at the 34 unfold sites survive.
- `srvClusterBoot_alloc` already has `Hnd : ps.Nodup` and `γ.vs = ps` (`NewServerAlloc.lean:157,
  165`), so its premises do not change. `NewServerAllocOn`'s twin is changed the same way.
  `srv_first_boot` destructures it.
- A restarted member reuses it: it is the cluster's.
- Cost: `SrvRaftLog.lean` has 1370 importers: one full build.

**F4: one spec of `run`.** It belongs in R2c (Q4), because the stop chain stays a set of draft
hypotheses (`Start_builtS_spec`) until `Start` gives the stop right. It needs four things:
1. Item 1 carried in the request (above).
2. F-e's readers in the request.
3. The slot reachable from `start`. Recommended (Q5): `srvStop.keep` moves into `NewServer`'s built
   part (`srvBuiltG` → `isServerBuiltC`), the slot convention's place for a subsystem's
   `srvInv`, so that no `Start` caller passes it. This is a hub request to etcd-grove-82.
4. `start` makes `stop`/`done` with the stop's predicates (`srvStopReq`, `srvDoneInv`) and `Start`
   posts `srvStopRight`.

Then:
- `run.spec` is today's `specStop` without the scope conjunct (one statement). `wp_proofG`'s flag
  goes.
- `Start_builtS_spec` is deleted: `wp_Start_built` gives the right (D3).
- A client that never stops drops the right (affine).

The restart's change to `run` (F-a, F-b, in R2d) touches `%HEr` only, not the stop's parts.

**Item 3: a restarted member's `run`, and the KV invariant at restart: R2d** (Q1). What R2d's Scope
starts from:

| piece | what it needs | source |
|---|---|---|
| `run` at restart | `%HEr` generalized: `ai₀ = σ.b`, `c₀ = i`, `σ.b ≤ i` (F-a); `γn.pre` a prefix of the server's log of length `σ.b`, the server's names kept at `pre = []` (F-b); the replay window `(σ.b, i]` through `applyEntries`' `ApplyV2storeOnly` branch (to check: guess, `ciJ`'s first disjunct already admits `c₀ > ai`, `InvRunRes.lean`); a conf entry in the window calls `AddMember` of a present member (open since the image review) | `EtcdServer__run.lean` (22 sites), `applyEntries` |
| the KV at restart | `x₀` the store `mvcc.New` restores from the image `D` (`store.restore`, proved) at index `i`; `kvInv` reused by `kvInv_congr` with `restartNames` widened to its 11 fields (F-c, Q8); the restored store's log bound from `soleWriter_small'` | `NewServer`'s restart case |
| `NewServer` over a restart boot (L5) | one spec over both boots: `bootOk`/`bootOkR` merged into one contract over the directory's state (the whole-`bootOk` review's F, deferred to R2d); `memStorRestarted` defined, giving `RestartNode`'s `restartStorage`; `newRaftNode`'s `RestartNode` path; the member's new incarnation key (`idIncarnation_alloc`) | the boot hub |
| `Start_builtR_spec`, `specRestart` | the above | `etcdstart` |

**Item 4.**
- `BuildServer.specStop`: R2c, by merging it into `BuildServer.spec` (Q7). There is one spec, whose
  post is `memberBuilt … ∗ leaseTTLRowR s ps ∗ srvDataDir s (name ++ ".etcd")`; the slot is in
  `memberBuilt`'s built part (Q5).
  - `srvDataDir` comes from a new slot law `srvStop.dataDir` (the slot's read-only `DataDir` and
    `DedicatedWALDir` fields at the values `memberFreshRes_boot` fixes, D2). It is posted by
    `newServer`/`newServerMode`.
  - Those two posts are frozen statements (below).
  - `memberBuiltS` and `memberBuilt`'s `K` become redundant: `K` goes, which coordinates with D4
    (lease-expiry's `fresh` flag on `memberBuilt`).
- `BuildServer.specRestart`: R2d, as a case of the merged `BuildServer.spec` once `NewServer` has
  one spec over both boots.

#### The statements touched (recommended options)

FROZEN marks a statement in `hub-step7-frozen`'s set: per the rule "frozen changes found in a later
stage's Draft come in one batch", these go to the user as one list at R2c's Freeze. HUB marks a
hub statement: a request to etcd-grove-82.

| statement | file | old | new | kind | flag |
|---|---|---|---|---|---|
| `srvRaftLogInv` | `etcdserver/SrvRaftLog.lean:740` | `∃ ps, ps ≠ [] ∧ srvBootLogOk ps boot` | `vs ≠ [] ∧ vs.Nodup ∧ srvBootLogOk vs boot` | invariant body, stronger | (1370 importers) |
| `srvStop.scope` (new), `srvStop.scope_of`, `srvStop.dataDir` | `etcdserver/StopApi.lean` | — | sealed fact and laws | server API (interface regenerated) | |
| `srvStop.keep` | `StopApi.lean` | four parts | + `□ (⌜in scope⌝ → srvStop.scope s)` | sealed body | |
| `srvStopRight`'s bag | `InvRestart.lean:206` | `fun _ => srvBootApplied ρ` | `fun _ => srvStopReq s ρ` (+ scope, + 128 readers) | def body | |
| `srvShutdownPre` | `StopApi.lean:185` | slot ∗ `srvDataDir` ∗ 128 readers | the slot only, or gone (the slot in the built part) | def | |
| `isServerRun` | `InvRun.lean:40` | `SP := False`, `DQ := True` defaults; `%HEr` | the stop's `SP`/`DQ`; `%HEr` + `Er.ST = srvTrStopK γk` (D1) | aggregator | HUB (`isServerBuilt` family) |
| `run.spec`, `run.specStop` | `Spec/.../EtcdServer__run.lean:38,71` | two specs; `specStop` with five pure premises | one spec: `specStop`'s shape, no scope premise | F4 | |
| `HardStop.spec` | `Spec/.../EtcdServer__HardStop.lean:42` | `srvStopRight ∗ srvBootApplied ρ` | `srvStopRight ∗ srvStopReq s ρ` | spec (draft, R2a) | |
| `NewServer.specG`'s post | `Spec/.../NewServer.lean:361` | `… ∗ srvStop.keep srv cfg E γrn γk` | the slot inside `srvBuiltG` | text, same content | HUB |
| `EtcdServer.start.spec`, `Start.spec` | `Spec/.../EtcdServer__start.lean:47`, `EtcdServer__Start.lean:41` | post: the request and read views, … | + `srvStopRight s ρ.rd.raft.raft ρ id dd` (at the slot's `DataDir`) | post, stronger | HUB (45 files name `Start.spec`; mostly via `wp_Start_built`) |
| `newServer.spec`, `newServerMode.spec` | `Spec/.../etcdstart/newServer.lean:87`, `newServerMode.lean:79` | `memberBuilt … ∗ leaseTTLRowR s ps` | + `srvDataDir s (name ++ ".etcd")` | post, stronger | FROZEN |
| `BuildServer.spec`/`specStop` | `Spec/.../etcdstart/BuildServer.lean:48,89` | two specs | one (`specStop` deleted), post + `srvDataDir` | merge | FROZEN (S7) |
| `memberBuilt`, `memberBuiltS` | `etcdstart/Defs.lean:306`, `Restart.lean:59` | `K` parameter, `memberBuiltS` | `K` gone (the slot is inside `isServerBuilt`); `memberBuiltS` = `memberBuilt` | exported def in frozen statements | FROZEN (meaning); coordinates with D4 |
| `wp_Start_built` | `etcdstart/Start.lean:38` | post `memberUp` | + `srvStopRight …` | proved lemma | |
| `Start_builtS_spec` | `etcdstart/StartStop.lean:53` | draft hypothesis | deleted (D3) | — | |
| `memberStop` (restart) | `examples/etcd/restart/Defs.lean:139` | `srvStopRight …` | + the scope and the member's 128 unused serving readers (from `memberUp`, a new law) | def in the frozen `stop.spec`/`startMember.spec` | FROZEN (meaning) |

**Unchanged in R2c:** `srvDiskImage`, `bootstrapRestartContract`, `bootOkR`, `restartNames`,
`BuildServer.specRestart`, `startMember.specRestart`, `Start_builtR_spec` (R2d's), every closed
theorem, `startRights`.

#### The trust base

- **R2c as recommended adds no axiom, no trusted model and no premise to an exported statement.**
  - The scope moves from a draft spec's precondition into a request that `restart3` proves.
  - `srvStop.scope` is proved from `NewServer`'s configuration.
  - `etc/tcb-report.py --check` should match the baseline.
- **Hard stops only in the alternatives:**
  - Q2's fork reorder of `Cleanup` (compactor before backend) is a fork change.
  - Any closed theorem for `restart3` (A4) takes `bootstrapRestartContract` (a trusted contract)
    and `http.ListenerClose_spec` (a draft boundary that becomes an axiom), and needs the data
    directory's exclusivity (the whole-`bootOk` review's E: a durable-directory GooseLang
    extension). Each is trust-base growth, with the `axiom` skill's attack before its Freeze. That
    is R2d's Scope.

#### The closed theorem (A4)

Not in R2c. `restart3_safe` needs:
- R2d's restart chain (`specRestart`, `Start_builtR_spec`, `run` at restart);
- the raft wrapper's `RestartNode` path;
- the catch-up after the restart (L6: a snapshot to the restarted member);
- the trusted items above.

The hub plan's A4 (`etcd_adequate_members` at the three members, `Bs := []`, `runRes` unfolded) is
the easy part and stays as written.

#### Sub-steps, in order (R2c as recommended)

| step | what | files (est.) | lines (est.) | effort | full build? |
|---|---|---|---|---|---|
| R2c-1 | item 2: `srvRaftLogInv`'s conjunct; `stop_imageConf`'s `hvs` from it; `run.specStop`'s boot-log premise gone | 4 | 40 | small | yes (`SrvRaftLog`) |
| R2c-2 | item 1: `srvStop.scope` and its laws, `srvStopReq`, `srvStopRight`'s bag, `HardStop.spec` and proof; `stopCleanupImage.spec`'s scope from the request; the 128 readers from the request; `restart`'s `memberStop` and `stop` (a `memberUp` law for the unused stocks) | 8 | 250 | medium | yes (`StopApi`: 717 importers) |
| R2c-3 | Q5: the slot into `srvBuiltG`/`isServerBuiltC` (hub request); `NewServer`'s proof moves the conjunct; `memberBuilt`'s `K` gone | 10 | 150 | medium (plumbing) | yes |
| R2c-4 | F4: `start` makes the stop's channels; `start.spec`/`Start.spec` post the right; one `run.spec`; `wp_Start_built`'s post; `Start_builtS_spec` deleted; `Link`/`Results` regenerated; interfaces | 15 | 300 | medium-large (`start`'s proof, 615 lines; 45 `Start.spec` files mostly mechanical) | yes |
| R2c-5 | item 4a: `srvStop.dataDir`; `newServer`/`newServerMode` post `srvDataDir`; `BuildServer` one spec, proved; `restart.startMember.spec`'s proof over it and `wp_Start_built` | 6 | 80 | small | no (etcdstart, 49 importers) |
| Review/Test/Probe/Freeze | a fresh reviewer on the stop chain (the request, the slot's move, one `run`); the frozen-change batch (FROZEN rows) and the hub requests to 82; probes: R2c-2's stop branch (hard), R2c-5 (easy) | — | — | — | — |

Total (est.): about 40 files and 800 lines, four full builds (R2c-1 to R2c-4 can share one if they
land together). Glue (Draft's list, the "decides nothing" rule): R2c-5's `BuildServer` proof and
`startMember.spec`'s; the rest is invariant and spec work for Prove.

#### Alternatives (Q1)

- **(A) Recommended:** R2c = the stop chain (items 1, 2, 4a, F4); R2d = the restart (item 3, 4b,
  A4). R2c is about a week of agent work (est.), lands no trust, and makes the stop
  one spec per function.
- **(B) The brief as written:** one stage for all four.
  - Its Freeze would cover the boot hub's restart case (`NewServer` over both boots, the merged
    `bootOk`/`bootOkR` contract: a trusted statement restated, a hard stop) together with the stop.
  - Its size is L5's, the plan's largest but one (est. 3-5× (A)).
  - It holds the stop's landing hostage to the restart's design.
- **(C)** (A), plus the restart's statements drafted (R2d's Draft started early, no proofs). It
  saves little: R2d's Scope must still decide F-a to F-c, Q8, Q9 and the boot-contract merge.

#### Risks, and what would make us revise

- The hub requests (Q5, the `Start` post) are refused or conflict with another session's hub change
  (D4 on `memberBuilt`, etcd-grove-c9): fall back to Q5 (b), `Start.spec` taking the slot as a
  separate precondition. That touches every `Start` caller's statement.
- `start`'s channel allocation cannot give the bag a non-persistent payload (the readers). Then the
  readers go in `HardStop`'s own precondition and `run` receives them through the escrow. That is a
  guess to check in R2c-2's probe.
- `srvRaftLogInv`'s positional patterns break more widely than the 34 unfold sites suggest.
- The user wants an auth-on or compaction-mode stop soon: lift that premise in R2c instead of
  carrying it (medium each; auth on also hits gap H in R2d).
- F-a's replay window turns out unproved on the apply path (`ApplyV2storeOnly`): it affects R2d's
  size, not R2c.
- Lifting the compactor premise later by a share-free reader changes the compactor's slot (the
  k8s compactor's specs): K-track coordination.

### R2c Draft (2026-11-06, branch `r2c`; frozen 2026-11-06, tag `r2c-frozen`)

**Frozen** as listed in the Freeze package (S1-S3, statement changes 1-21, Q3/Q4/Q6/Q7, D1-D3,
D-a-D-f): decided by etcd-grove-82 under the user's delegation (user offline), 2026-11-06, pending the
user's review.

Sub-steps R2c-1 to R2c-5 as in the Scope (A), proved, no `sorry`, no axiom: `e086ccfcc9` (R2c-1),
`4623b75b93` (R2c-2), `84792dae13` (R2c-3), `53b9d60e74` (R2c-4), `5fd553525e` (R2c-5). What changed
and why: `notes/decisions.md`, "The stop chain for a first start". The agent's decisions D-a to D-f
(pending the user) and every frozen or exported statement touched, old → new, are in the
worktree's `questions.md` (the Freeze batch). Departures from the Scope:
- **D-d (Q5 adapted, no hub request):** the slot (`srvStop.slot`) is a conjunct of `isServerBuiltC`
  and `isServerRunC`, not of `srvBuiltG`/`isServerBuilt`/`isServerRun`: the import graph
  (`StopApi → InvRestart → InvStart → InvRun`) forbids those. `NewServer.specG` is unchanged.
- **D-c:** the 128 serving readers are the stop request's (`srvStopReq`), so the right's `E` must be
  the serving stocks': `etcdstart.memberUp` holds the right (its last conjunct), and the restart
  example splits what the stop needs (`memberStopRes`: the right, the scope, the readers) off
  `memberUp` by `memberUp_stopRes` (out of compaction mode). `restart`'s `memberStop` keeps only the
  data directory record.
- **D-f:** `done`'s content is the escrowed image, not `True`: `srvDoneChan` and the read loop's
  `srvChanOk` quantify the channel's predicate.
- `Start_builtR_spec`'s post is `memberUp` (the right inside it); `restart.startMember.spec` gains
  `BuildServer.spec`'s UTF-8 premise on the initial cluster's names (the draft `specStop` lacked it).

**The trust base (a hard stop at the gates, decided by the user on 2026-11-06, option (a), relayed
by etcd-grove-82):** the one `run.spec` contains the stop branch, so every result through `run`
reaches the three axioms of the image's configuration (`apply.memberKey_inj`,
`apply.memberEnc_id_learner`, `membership.membersOf_decode`). The user reviewed them on 2026-11-04
(R2b-3d gap 3), but until now only the draft `run.specStop` used them. The path is
`stop_cleanup_image` → `stop_imageConf` → `RestConf.restModel_confState`. The trust base goes from
785 to 788 axioms. The baselines are updated: the global one and 14 collections, which also gain
`lease.lessor.Stop.wp_proof`. The bounds gate
holds (`srvStopReaders`, the stop's owner's name for the readers' count).

**Review round 1 (2026-11-06, a fresh `spec-reviewer`, `/shared/tmp/r2c-review.md`):**
- F1: the R2d drafts no longer duplicate the slot.
- F2: `raftNode.stop` has one spec.
- F3: the stop's scope restriction is stated: only a member that never served gRPC can be stopped.
- F4: clients use laws, not unfolds.
- F5: `srvStopRight` is sealed.
- F6-F8: docstrings.

Details are in `notes/decisions.md`, "The stop chain for a first start".

**Left (R2d):** a restarted member's `run`, `Start_builtR_spec`, `BuildServer.specRestart`,
`startMember.specRestart`, Q8, Q9.

**Review round 2 (2026-11-06, `/shared/tmp/r2c-review2.md`):** all of round 1's fixes were found in
place. Six low findings:
- N1: the dead `srvDataDir` premise is dropped from `Start_builtR_spec`.
- N2: `InvRestart` is sealed in `etc/import-all.txt`; only `start`'s and `HardStop`'s proofs
  `import all` it.
- N3: new law `srvWatchReaders_storeReaders`, and `srvStopReaders_intro` moves to its own module
  `StopReaders`, so `StopApi` does not import the watch vocabulary.
- N4: stale text, including `HardStop`'s scope now matched against etcd's `embed`.
- N5: `srvStop.slot_intro` takes its fact as a Lean premise.

**Left for etcdstart's owner (N6):** 16 example proofs take `etcdstart.memberUp` apart by position:
- `txnlin`, `leasegrant`, `leaseexpiry`, `watch`, `putget3` (×3), `cache`, `compacted`,
  `compactwatch`, `lease` and `putget` (their `Main`);
- `restart/Run` and `restartCheck`;
- `k8s/compactor` and `k8s/etcd3`;
- `cluster3/StartMember`.

Laws such as `memberUp_serve` or `memberUp_kvStocks` would make the next conjunct added to
`memberUp` a local change (R2c-4 had to touch three of them).

### R2d Scope (2026-11-06, for the user)

Session etcd-grove-83, branch `r2d` (off `lean` `6b49f77e01`, after R2c's Freeze, tag `r2c-frozen`).
Design only: no Lean edited, nothing built. **A hard stop: the user's Scope.** The questions are in
the worktree's `questions.md` (untracked); the coordinator's package is
`/shared/tmp/r2d-scope-package.md`. Line numbers are at `6b49f77e01` (Go: the etcd pin, `249d76bea7`).
Sizes are estimates (marked "est.").

**The brief** (the coordinator's): a restarted member's `run`; `Start_builtR_spec`;
`BuildServer.specRestart`, `startMember.specRestart` and `NewServer` over both boots; A4 (the restart
example's closed theorem, `examples/etcd/restart/restart3.go`); Q8 (the KV invariant at a restart);
Q9 (a restarted `run`'s starting point); and a check of R2c's finding that A4 needs three new
trusted assumptions.

**The recommendation, in one paragraph.** Split. **R2d** is the server's restart chain, proved over
the existing trust base plus **one** widened axiom (`NewAuthStore` over the auth bucket a first start
leaves, a hard stop): Q8 (a), Q9 (d) (below; R2c's leaning (a) does not typecheck as written), one
`NewServer` spec over both boots, `BuildServer` with one spec, `startMember` with one spec, and
`Start_builtR_spec` deleted (the ordinary `Start.spec` covers a restarted member). **R2e** is A4: the
closed theorem `restart3_safe`, which brings the remaining trust items (the restart contract as a
premise, `ListenerClose` and the widened `register`, the data directories' exclusivity), the
restarted member's catch-up, and its `Link`/`Results`. gRPC `GracefulStop` is neither: its own stage,
after R2e. The old label "R2e raft's restart" is retired (`RestartNode` is proved). Estimate: R2d
3-4 weeks (est.; about 45 files, 2500-3500 changed lines, two full builds per round at most), R2e
1-2 weeks (est.) plus its trust Freeze.

#### What reading the code found

- **G-a. Q9's leaning (a) is inconsistent with the names a restart keeps.** A member's names are the
  cluster's: `isServer` has `⌜ρ.rd = γr⌝` (`InvApplier.lean:664`), `NewServer` fixes
  `ρ.rd.raft = ⟨γ, [], W64 0⟩` (`NewServer.lean:162`) and `ρ.rd.kv.c0 = 0` (`:166`), and
  `restartNames` keeps both (`InvRestart.lean:582-585`). `kvRun γr ai₀ c₀ A x` forces
  `γr.kv.c0 = c₀ ∧ γr.raft.ai0 = ai₀` (`InvRunRes.lean:256`), and `srvRaftLogInv` fixes
  `γ.pre = []`, `ai0 = pre.length` (`SrvRaftLog.lean:742`). So (a)'s `ai₀ = σ.b`, `c₀ = i` holds only
  at `σ.b = i = 0`. Making it hold needs new raft and KV names per incarnation, which Q8 rules out
  (G-b).
- **G-b. A second `kvInv` cannot be allocated.** `kvInv` (`InvRequest.lean:673`) holds the only
  invariant half of the ghost variable `γk.st` and `srvRLog γ L` (the cluster's mono-list half,
  `SrvRaftLog.lean:386`), and `uint.Z γk.c0 ≤ uint.Z γ.ai0` (`InvRequest.lean:676`): a member's
  `kvInv` at `c0 = i` over the cluster's `ai0 = 0` is false. Q8 (b) is out.
- **G-c. A restarted `run` lags its own KV.** `run` sets `ep.appliedi` from raft storage's snapshot
  (`server.go:760`, `:808-814`): the WAL snapshot's `σ.b`. The backend holds the KV through its
  consistent index `i ≥ σ.b` (`srvDiskImage`, `InvRestart.lean:130`). `applyEntries` skips only
  entries `≤ ep.appliedi` (`:1215-1239`), so `(σ.b, i]` is applied again, each with
  `shouldApplyV3 = ApplyV2storeOnly` (`:1939-1943`, `e.Index <= ConsistentIndex`), which writes no
  KV. The model already has this shape: `batchStep`'s `v3 = decide (c < m.index)`
  (`InvApplier.lean:221`), `loopOk`'s `p = max ciEff a` (`:105`), `ciJ`'s second disjunct
  (`InvRunRes.lean:56`), and the snapshot install's jump (`applied_jump`, `InvRequest.lean:2284`;
  `kvApplied_of_jump`, `snapRecv_kv_jump`), where the ghost applied index runs ahead of Go's.
- **G-d. The replay window is not invisible to the rest buckets' in-memory model.** With `v3 = false`:
  `apply` still calls `Apply` (`server.go:1975-2006`); the uber applier dispatches
  `ClusterVersionSet`, `ClusterMemberAttrSet` and `DowngradeInfoSet` before its `!v3` return
  (`apply/uber_applier.go:82-127`); `UpdateAttributes` and `SetVersion` set the in-memory
  attributes and version even when v2-only (`membership/cluster.go:467-477`, `:589-623`);
  `applyConfChange` still calls `SetConfState` and `transport.AddPeer` (`server.go:2037-2110`) while
  `AddMember` v2-only is a no-op (`cluster.go:394-425`), and a replayed removal of the member itself
  still returns `removedSelf = true` (`server.go:2087-2089`), so `apply` returns `shouldStop`
  (`:1959`) and `applyEntries` stops the server (`stopWithDelay`, `:1236-1237`) (added 2026-11-06, the
  Freeze 1b review's N5; line numbers in G-c/G-d at the pin `673da07c8`). So during the window the in-memory version
  and attributes go back to older values and forward again; at the window's end they are the
  image's again (last writer wins over the same entries). `restAfter`/`restUpdateAttrs`
  (`apply/RestModel.lean:118-128`) already model the v3-false writes. A documented behavior
  (`shouldApplyV3`'s comment), not a bug: nothing filed.
- **G-e. `s.appliedIndex` starts at 0 at a restart.** `setAppliedIndex` (`server.go:1719`) is the only
  writer; nothing sets it from `ep.appliedi` before the first batch. Readers of `AppliedIndex()`
  (the read-index loop's wait, `linearizableReadLoop`) see 0 until the first applied entry.
  `srvAppliedBody` already lets the atomic lag the ghost (J5, `InvRequest.lean:2141`); the restart
  is that case from the start. Not a bug (a reader waits longer).
- **G-f. Three constructor axioms are stated on empty buckets.** `NewAuthStore.spec` takes the auth
  bucket `∅` (`Spec/.../auth/NewAuthStore.lean:125-126`); a first start leaves `authBoot`
  (`authRevision = 1`, `InvRest.lean:280`), which is what a restart reads. `NewLessor` (`lease`
  bucket `∅`, `NewLessor.lean:141`) and `NewAlarmStore` (`alarm` bucket `∅`,
  `NewAlarmStore.lean:86`) are met by the image as it is: the server's workload (`plainCover`)
  leaves them empty (`InvImage.lean:249-254`). So R2c's count of three new trusted items is short
  by one, `NewAuthStore`'s widening, and it falls in R2d, not A4.
- **G-g. `mvcc.NewStore` and `mvcc.New` are specified on a fresh backend only**
  (`Spec/.../mvcc/NewStore.lean:2`, `:27`). A restart needs the restoring case; `store.restore` is
  proved (the snapshot path), so this is proof work, no trust.
- **G-h. Under (d) the hub's `start`/`Start` statements keep `ai₀ = W64 0`**
  (`EtcdServer__start.lean:55`, `EtcdServer__Start.lean:47`): the applier's context indices are the
  names' (0), and Go's lagging `appliedi` lives inside `applyRes`. What changes is the meaning of
  `isServerBuiltC`/`isServerRunC` (and `start`'s docstring, "from index `0`").

#### 1. What R2d verifies

| Option | Content | Trust | Size (est.) |
|---|---|---|---|
| (A) one stage | the restart chain and A4 | 4 hard stops in one Freeze | 5-6 weeks |
| **(B) split, recommended** | R2d: the chain over both boots; R2e: A4 | R2d: 1 (`NewAuthStore`); R2e: 3 | R2d 3-4 weeks, R2e 1-2 |
| (C) three-way | R2d: `run` at restart only (Q9); R2d': `NewServer`/`BuildServer`; R2e: A4 | as (B) | as (B), one more Freeze |

(B) keeps each Freeze's trust items to those its own statements need, and R2d's result
(`BuildServer.spec` over both boots, `Start.spec` unchanged in text) is usable by any example, not
only `restart3`. (C) puts `run`'s and `NewServer`'s halves of one interface (`isServerBuiltC`'s
meaning) in different Freezes, so a change found in the second reopens the first.

**R2d's results:**
- `run.spec` (one, frozen in R2c) proved at a restarted member's starting point (Q9 (d)).
- `NewServer.specG` over both boots: a `boot` argument, first start (as now) or restart from
  `srvDiskImage` with `bootstrapRestartContract`'s `bootOkR`; the restart case reuses the cluster's
  `kvInv` (Q8 (a)).
- `newServer`/`newServerMode`/`BuildServer.spec` over both boots; `BuildServer.specRestart` merged
  into it; `memberBuiltR` merged into `memberBuilt`.
- `start.spec`, `Start.spec` unchanged in text; `Start_builtR_spec` deleted (the restarted member
  is an ordinary built member).
- `examples/etcd/restart`'s `startMember` with one spec (the restarted call uses the restart boot).

**Not R2d (R2e):** `restart3_safe`, its `Link`/`Results`; the catch-up check; the trust items
`bootstrapRestartContract` as an exported premise, `ListenerClose_spec` with the widened `register`,
and the data directories' exclusivity.

#### 2. Q8 and Q9

**Q8, the KV invariant at a restart.**
- (a) **Recommended.** Reuse the cluster's `kvInv` through `kvInv_congr` (`NewServerAlloc.lean:70`):
  widen `restartNames` to `ρ'.rd.raft = ρ.rd.raft ∧ kvCongr ρ.rd.kv ρ'.rd.kv ∧ …ids`, with
  `kvCongr` a new definition that is exactly `kvInv_congr`'s 11-field hypothesis (`st`, `c0`, `ch0`,
  `log0`, `ids.issued`, `ids.wn`, `cmp`, `rlog`, `cret`, `lm`, `kvPfx`), so the two cannot drift.
  The member's own names (`cok`, `hi`, the wait and the slots) are new. The revroom-b requirement
  (`kvInv`'s `log0` bound at a restart allocation) does not arise; the restored store's own bound
  comes from `soleWriter_small'`, as on the snapshot path (`SnapSendBranch.lean:357`). R2c's leaning
  (a) re-checked: right, but `restartNames` as written covers 6 of the 11 fields.
- (b) Allocate a member `kvInv` with `log0` the backend's log: impossible (G-b).

**Q9, a restarted `run`'s starting point.**
- (a) R2c's leaning: `%HEr` (`InvRun.lean:53-54`) generalized to `ai₀ = σ.b`, `c₀ = i`,
  `γn.pre` the first `σ.b` entries, the server names kept. **Inconsistent** (G-a).
- (b) Require `σ.b = i`: false of Go (`restart3` snapshots every other entry, `restart3.go:7-8`; the
  backend commits past the snapshot).
- (c) A window in the KV relation: `kvApplied`'s `A` the Go-applied entries and `x` ahead by
  `(ai, c]`. Changes `kvRun`, `kvApplied` (21 files), `kvBatch`, `appliedLogAt` (24) and `kvLogsOk`
  on the read path, and the stop's image. Large, and the read path would see the window.
- (d) **Recommended. The restart is a jump.** The ghost applied log starts at the backend's
  consistent index: `A₀` the committed entries through `i` (`imageAt` gives them,
  `InvRestart.lean:563`), `kvApplied γr.raft γr.kv A₀ x₀` as after a snapshot install
  (`kvApplied_of_jump`). The applier context's `ai₀ = c₀ = 0` stay (the names'), so `ciJ`, `loopOk`
  and `run_snap_job`'s `ha00`/`hc0` hypotheses (`EtcdServer__run.lean:297`, `:504`, `:681`) hold
  unchanged. Go's `ep.appliedi = σ.b` lags: `applyRes` gains `aiGo ≤ ai` with
  `epAppliedIAddr C.ep ↦ aiGo`, equal to `ai` past the window; the window's entries are replays of
  entries of `A₀` (`entryStep … v3 = false`, KV unchanged). `%HEr`'s `γn.pre = []` becomes a prefix
  relation (the node hands from `σ.b`, `RestartNode.spec`), `srvC`'s `srvRLogLb ρ.raft L` becomes
  `srvRLogLb ρ.raft (P ++ L)` with `P = γn.pre`, and `srvRest` gets a window form (G-d). The same
  form covers a merged snapshot labeled below its backend's index (a restarted leader in its window).
- What depends on it: `applyStart`, `applyRes`, `srvC`, `srvRest` (`InvRunRes`, 936 importers;
  `InvRest`, 1288, only by new lemmas in a new module); `setAppliedIndex.spec` (386) gains a
  below-ghost case (the atomic stores `aiGo`); `run`'s proof (48 `pre` and 74 `ai₀` mentions).

#### 3. gRPC `GracefulStop`

**Later, its own stage after R2e; not needed by `restart3`** (only member 1 serves before the
restart, `restart3.go:85-86`; S1 of R2c).
- No spec of `Server.Stop`/`GracefulStop` exists; grpc is names-only (`Code/google_golang_org/grpc.toml`).
  The serve axioms (`grpc.serve`, `InvGrpc.lean:928`; `serveStream`, `InvGrpcStream.lean:1043`)
  consume the serving stocks for good (post `True`).
- What it waits for (grpc-go v1.84.0 `server.go:1687-1729`): `GracefulStop` closes the listeners,
  drains the transports and waits for `handlersWG`; `Stop` does not wait for handlers unless
  `WaitForHandlers`. etcd calls `GracefulStop` under a `ReqTimeout` context and falls back to `Stop`
  (`embed/etcd.go:436-446`, `:490-521`).
- Watch streams do not end at `GracefulStop` (`v3rpc/watch.go:220-233` returns only on the stream's
  context), and `recvLoop` outlives `Watch` (`:194-198`, the code's own comment), so the watch
  slots cannot be returned at a handler's end: a fork change or a weaker claim.
- Unary methods return their slots (`grpcMethodOkMd`); Watch keeps them (`grpcStreamMethodOk`; the
  returning variant `grpcStreamMethodOkR`/`grpcSlotPool` is unused). 9 `v3rpc` spec files name the
  serving readers.
- Estimate: 1-2 weeks (est.), two hard stops (a new axiom family for `Stop`/`GracefulStop`; the watch
  path's claim).

#### 4. Frozen statements R2d changes (old → new)

At `r2c-frozen`, `hub-step7-frozen` or exported. **[HUB]** marks a request to etcd-grove-82.

1. **[HUB]** `NewServer.specG` (`NewServer.lean:147`): the first start's names hard-coded
   (`:162-167`) → a `boot : SrvBoot` argument: `.first` as now (premises `bootstrapContract`,
   `wal.bootRes`, `nodeBoot`, `srvReadNamesFreshNK`), `.restart ρ σ i L D` with
   `bootstrapRestartContract`, `srvDiskImage` and `restartNames`; one post. A closed theorem at a first
   start instantiates `.first` and gains no premise.
2. **[HUB]** `bootOk`/`bootOkR` (`InvRestart.lean:357`): unchanged as two contracts (the
   trust-boundary exception: a fact only the trusted contract gives is taken only by the case that
   needs it); `memStorRestarted` (`:331`, opaque) becomes a definition, restating what
   `bootOkR` gives of raft's memory storage (`bootstrap.go:725-734`). The merge of `lateWB`/`lateWBR`
   (B1) is restated, not merged.
3. **[HUB]** `isServerBuiltC`, `isServerRunC` (`InvBuild.lean:316`, `InvRun.lean:53-54`, and the
   `%HEr` copies in `InvStart.lean:240`, `StartOn.lean:87`, `StopShutdown.lean:414`): text of
   `%HEr` `c₀ ≤ ai₀ ∧ γn.pre = [] ∧ ai₀ = 0` → `c₀ ≤ ai₀ ∧ ai₀ = 0 ∧ γn.pre <+: …` (the prefix
   relation), and `applyStart` at an initial `A₀`.
4. `start.spec`, `Start.spec` (hub / exported): text unchanged (G-h); meaning through item 3. The
   docstring's "from index `0`" changes.
5. `run.spec` (`r2c-frozen` 12): text unchanged; meaning through item 3; docstring scope "a first
   start" → "a first start or a restart".
6. `newServer.spec`, `newServerMode.spec`, `BuildServer.spec` (`hub-step7-frozen`, R2c 1-2): gain the
   boot argument; `BuildServer.specRestart` merged in and deleted.
7. `etcdstart.memberBuilt` (`Defs.lean:308`): over both boots; `memberBuiltR`, `bootPremiseR`
   (`Restart.lean`) merged; `memberRestartRes` (`StartRes.lean:94`) kept as the restart boot's
   premise.
8. `restartNames` (`InvRestart.lean:582`): widened (Q8 (a)). `srvDiskImage` (`:130`): unchanged.
9. `Start_builtR_spec` (`StartStop.lean`, draft): deleted.
10. restart's `startMember.spec`/`specRestart` (R2c 7): one spec with the boot argument.
11. Internal: `applyStart`, `applyRes`, `srvC`, `srvRest` (window form), `setAppliedIndex.spec`
    (below-ghost case), `mvcc.New.spec`/`NewStore.spec` (a restoring case), `newRaftNode`'s spec (the
    `RestartNode` path; 788 importers).
12. **Trust** `auth.NewAuthStore.spec` (axiom): hard stop HS1 below.

**Scope amendment (2026-11-06).** Item 11 gains `applyAll.specBatch`, `kvBatch`,
`applyEntries.specBatch` and `apply.spec` (a window form of each, one spec per function), because
the hard probe failed (Q13, answer (a), decided by etcd-grove-82 under the user's delegation, pending
the user's review): every spec of the apply chain tied Go's applied index to the ghost log's
length. Conditions (etcd-grove-82): each window form reduces to today's text when there is no
window (`aiGo = ai0 + |A|`), by a law first-start callers rewrite with; the snapshot install's
`applied_jump` vocabulary is reused, with no second notion of replay; the four statements and the
reduction laws are their own Draft round, reviewed before `run`'s proof is touched; a change they
force on a frozen or exported statement is a stop.

#### 5. Trust-base impact

R2d adds no axiom and widens one. R2e's three are listed so the user sees the whole count.

- **HS1 (R2d). `NewAuthStore` over a first start's auth bucket.** In `auth.NewAuthStore.spec`
  (`Spec/.../auth/NewAuthStore.lean:111-137`) replace
  `(r.lookup go!"auth").getD ∅ = ∅` by
  `((r.lookup go!"auth").getD ∅ = ∅ ∨ (r.lookup go!"auth").getD ∅ = authBoot)`, all else unchanged
  (post: the bucket at `authBoot`, auth disabled). Why true: `NewAuthStore` (`server/auth/store.go:977-993`) reads
  `authEnabled` (absent in `authBoot`: disabled) and the revision (1), skips `commitRevision` (it
  runs only at revision 0), and `refreshRangePermCache` reads no user (`authUsers = ∅`): the store
  and bucket end exactly as after a first start, where `commitRevision` set revision 1. Attacks
  tried: an enabled bucket (excluded: the premise is equality to `authBoot`, which has no
  `authEnabled`); a non-empty users or roles bucket (excluded by the kept premises); a revision other
  than 1 (excluded); the store's in-memory revision differing between the two cases (no: 1 in both).
  None found a panic or a different post.
- **HS2 (R2e). `bootstrapRestartContract` as a premise of `restart3_safe`** (`InvRestart.lean:559-576`,
  as it stands, a persistent premise as `bootstrapContract` is for every closed theorem). Why true
  and its attack: the R2b whole-`bootOk` review's (M1 and the rest); to be re-attacked with the
  `axiom` skill before R2e's Freeze, on `memStorRestarted`'s definition (HS1's sibling: it must say
  only what `bootstrap.go:554-581` and `:725-734` do).
- **HS3 (R2e). `http.ListenerClose_spec` and the widened `register`** (`Proof/net/http/ListenerClose.lean`,
  drafts): `registerClosable_spec : netListenerAt l a -∗ httpProtoOwn a P ==∗ ⌜∃ li, l = ok li⌝ ∗
  httpListenerAt l a P ∗ httpListenerCloser l a P` (widens the axiom `register`, `Axioms.lean:45`)
  and `ListenerClose_spec : {{ httpListenerCloser l a P }} l.Close() {{ err; netAddrFree a ∗
  httpProtoOwn a P }}`. So R2c's "one" item is two statements. Why true: `FD.Close` waits until the
  descriptor is closed (`internal/poll/fd_unix.go:91-118`), and the listener sets `SO_REUSEADDR`
  (`net/sockopt_linux.go:28`), so the address can be bound again at once. Attacks tried: binding the
  address after `Close` (succeeds in Go, as claimed); a second `Close` (blocked: the closer is
  exclusive and consumed); making `netAddrFree` from nothing (no: it comes back only for the address
  `Listen` consumed, via the closer `register` produced).
- **HS4 (R2e). The data directories' exclusivity.** `walFiles` (`WalRecs.lean:178`), `fileHolds`
  (`InvBbolt.lean:102`) and `walDirFresh` (`WalDir.lean:27`) are axioms read as `True` in the start
  axiom's satisfiability argument (R2b-1 stage 3a). Options: (i) a durable-directory GooseLang
  extension (the whole-`bootOk` review's E); (ii) exclusivity axioms, e.g.
  `walFiles_excl : walFiles d id cid σ ∗ walFiles d id' cid' σ' ⊢ False` and
  `walFiles_fresh_excl : walFiles d id cid σ ∗ walDirFresh d ⊢ False`; (iii) the three defined over a
  per-directory ghost name that `goose_adequacy_start` allocates (`startRights`), restating that
  axiom; (iv) the members' directories distinct as a premise of `restart3_safe`, as `putget3`
  takes them. Attack on (ii): it breaks the `True` reading (`True ∗ True ⊢ False` is false), so (ii)
  is sound only with (iii)'s model: (ii) alone is rejected. Recommendation: (iv) if R2e's proof needs
  only distinctness (it reuses one member's `srvDataDir` and `srvFiles`, both exclusive resources
  already), else (iii). Decided in R2e's Scope.

Verified R2c's "three new trusted assumptions": the three are real (HS2-HS4), HS3 is two
statements, and HS1 is a fourth, needed already by R2d.

#### 6. Sub-steps

| Step | What | Files (lines) | Risk | Full build (`--count`) |
|---|---|---|---|---|
| R2d-1 | Q8 (a): `kvCongr`, `restartNames` widened, `HardStop` gives it | `InvRestart.lean:580-585`, `NewServerAlloc.lean:70`, `HardStop` proof | low | yes (732) |
| R2d-2 | Q9 (d) vocabulary: `applyStart` at `A₀`, `applyRes`'s `aiGo`, `srvC`'s prefix; `%HEr` | `InvRunRes.lean:184,256,404`, `InvRun.lean:53`, `InvBuild:316`, `InvStart:240`, `StartOn:87`, `StopShutdown:414` | high | yes (936) |
| R2d-3 | `srvRest`'s window form; last-writer-wins lemma | new `apply/RestReplay.lean` (no statement of `InvRest` changes) | high | no (new module) |
| R2d-4 | `setAppliedIndex.spec` below-ghost case | its spec and proof | medium | 386, with R2d-2 |
| R2d-5 | `run`'s proof over the generalized start (window batches, `run_snap_job` at `aiGo < ai`) | `EtcdServer__run.lean` proof and its lemma files | high | no (proofs) |
| R2d-3m | (**Superseded 2026-11-06 by R2s**, "R2d Draft, round 3" below and `notes/decisions.md`, "R2s: snapshots across windows": the design it carried is wrong, not unfinished.) (Q18 (c), decided by etcd-grove-82 under the user's delegation, 2026-11-06, pending the user's review) after R2d-5: the merged snapshot sent in a window and received (Q16 (3)): `srvNet`'s `img` at some `j ≥ i`, `srvSnapRO`'s key, `applyAll.specSnap`/`specSnapM`'s window posts and laws (`specSnapMNoWin`), the receive proofs from `i` to `j` (about 800 lines), `run`'s snapshot-job lemmas over the window, and `applyAll.wp_proofBatch`'s merged send at `W ≠ []` (until then a marked DRAFT sorry inside it). Its statements stay DRAFT until its own probe, then go to **Freeze 2** (R2d's Freeze is split: Freeze 1 everything else) | `InvApplyAll.lean:84`, `SnapRO.lean:452`, `InvRun.lean:113`, `EtcdServer__applyAll.lean` spec (146, 237), `ApplyAllSnap*.lean`, `SnapRecvFacts`, `EtcdServer__run.lean:299-730`, `SnapSendBranch`, `MergedImageOn`, `AuthCompRows` | high | yes (`srvNet`) |
| R2d-6 | Constructors over data: `mvcc.New`/`NewStore` restoring case; `NewAuthStore` widened (HS1); `newRaftNode`'s `RestartNode` path; `memStorRestarted` defined | specs `NewStore` (393), `New` (414), `NewAuthStore` (465), `newRaftNode` (788) | medium-high | yes |
| R2d-7 | `NewServer.specG` with the boot argument; proof's restart branch (`bootstrap.go:77` `haveWAL`, `:112`, `:437`) | `NewServer.lean` spec (462), proof (2865 lines) | high | 462 |
| R2d-8 | etcdstart: `memberBuilt` over both boots, `BuildServer` one spec, `Start_builtR_spec` deleted; restart's `startMember` | `Defs.lean:308` (188), `Restart.lean` (63), `BuildServer` (47), `StartStop.lean`, restart `startMember.lean` | low | no (188) |

Rounds: R2d-1, -2, -4, -6's statements in one batch (one full build), then R2d-3, -5, -7, -8 (proofs,
targeted builds), then the gates' full build.

**Review** (spec-reviewer, fresh, given the Go code and the callers, not this Scope's conclusions):
`applyRes`/`applyStart` at `A₀`/`aiGo`, `srvRest`'s window, `NewServer.specG`'s boot argument,
`restartNames`. **Test**: `restart3_test.go` passes at the pin; a Go test of the window (restart with
`σ.b < i`, the in-memory version read during the window) to confirm G-d. **Probe** (both proved in
the Draft): hard, `run`'s first window batch (`applyRes` with `aiGo < ai` and `srvRest`'s window
across one `ClusterVersionSet`); easy, R2d-1 (`restartNames` to `kvInv_congr`). **Freeze**: items
1-12 of section 4 in one batch, HS1 with the `axiom` skill's report.

#### 7. Risks, and what would make us revise

- `run`'s proof uses `ai₀` both for Go's fields (`ep.appliedi`, `ep.snapi`, `Hsnap` at `ai₀ at₀`) and
  for the ghost; separating them (74 mentions) is the bulk of R2d-5. If they cannot be separated
  locally, revise toward (c) for the applied index only.
- G-d's window: if the last-writer-wins argument fails for an interleaving of `UpdateAttributes` and
  a conf change in the window, `srvRest` needs a weaker form during the window, visible to readers of
  the members (a spec change on the read path).
- `NewServer`'s proof (2865 lines) may need restructuring for a second boot; if the restart branch
  shares little, give `NewServer` two specs under the trust-boundary exception instead of one.
- If `bootstrapRestartContract` must change to supply what R2d-7 needs (beyond defining
  `memStorRestarted`), that is a trust change in R2d: stop and ask.
- If the reviewer finds `imageAt`'s `A` insufficient to give `kvApplied … A₀ x₀` (the backend's log
  at `i`), the image's statement changes (`InvImage.lean`, a frozen predicate).

### R2d Draft, round 1 (2026-11-06, branch `r2d`)

Done, proved without `sorry` or a new axiom (`notes/decisions.md`, "R2d: the server's restart chain,
first round"; one full build after merging `lean` `aa4449beb6`):
- **R2d-1 (Q8 (a)).** `kvCongr` (`InvRequest.lean`), `kvInv_congr` over it (moved from
  `NewServerAlloc`), `restartNames` = raft's names, `kvCongr`, the ids' `issued`/`pfx`; the easy probe
  `kvInv_restartNames`; laws `restartNames_st`, `restartNames_kvModel` (`restartCheck` uses the
  first instead of a positional `obtain`).
- **R2d-4.** `setAppliedIndex.spec`'s replay case (`rep = true`, `v' ≤ v`: the ghost unchanged).
- **HS1.** `auth.NewAuthStore.spec`'s auth bucket `∅ ∨ authBoot`; `authUsers`/`authRoles` unchanged
  (etcd-grove-82's ruling); the attack is in the axiom's docstring and `notes/decisions.md`. The
  trust baseline lists axioms by name: no line changes.

**Stopped: the hard probe fails at the Scope's statement list (Q13, the worktree's `questions.md`).**
A window batch reaches `applyAll.specBatch` with Go's `ai = σ.b` and the ghost log `A₀` of length
`i`; `applyAll.specBatch` (`uint.Z ai = A.length`, `ciEff ≤ ai`), `kvBatch` (`ai = ai0 + |A|`),
`applyEntries.specBatch` and `apply.spec` all tie Go's index to the ghost log's length and append
the batch to it. (d) needs a window form of the four, which item 11 does not list. Not started
until the user answers: R2d-2 (its `applyRes`/`applyStart` shape is what the window form decides),
R2d-3, R2d-5, R2d-7, R2d-8. Independent of Q13 and left for the next round: R2d-6's constructors
(`mvcc.New`/`NewStore`'s restoring case, `newRaftNode`'s `RestartNode` path, `memStorRestarted`
defined). Coordination for the next round (etcd-grove-83, 2026-11-06): revoke-open lands first
and changes `run.spec`'s `threadTok`, `isServerRun*`/`isServerBuilt*`/`srvBuiltG`; R2d's `%HEr`
change goes in a named conjunct of its own, and the proofs use laws, not positional unfolds.


### R2d Draft, round 2: the window form and Q14 (2026-11-06, branch `r2d`)

*Superseded in part (2026-11-06, "R2d cut (Q21)" below): the window form (Q13 (a)) moved from R2d to R2d'; Q14 stays in R2d.*
*Reorganized (2026-11-06) by "R2d' Scope (approved 2026-11-06)" below: its R2d' contents are now that section's R2d'a/R2d'b items; where they differ, that section holds.*

**The split (Q15 (c), decided by etcd-grove-82 under the user's delegation, pending the user's
review): R2d / R2d' / R2e.** Supersedes the Scope's S1 split (`notes/decisions.md`, "R2d: the split
R2d / R2d' / R2e").
- **R2d** (this stage): `run` at a restart (R2d-2, -3, -5), the window form (Q13 (a)) and the WAL
  snapshot's certificate (Q14 (a)). R2d-6 shrinks to what `run` needs: `NewAuthStore` (HS1, done),
  `memStorRestarted` defined over the certificate (below), `newRaftNode`'s `RestartNode` path. R2d has
  no closed result.
- **R2d'** (after R2d, before R2e): `mvcc.New`/`NewStore`'s restoring case with the `lateWBR`/`lateWB`
  merge (B1), R2d-7 (`NewServer.specG` with the boot argument, its restart branch) and R2d-8
  (etcdstart over both boots). The `Hnew` row's trusted-text change is a hard stop at R2d''s Scope.
- **R2d' discharges `winNoConf`** (R2d review F1, decided by etcd-grove-82 under the user's
  delegation, 2026-11-06, pending the user's review; `questions.md`, "Assumptions R2d carries for
  R2d'"). R2d's restart `%HEr` carries the named conjunct `winNoConf W` (`ApplyWindow.lean`: no conf
  entry in the window; `winNoConf_nil` at a first start, `W = []`). R2d' removes it by proving the
  window's conf changes (`server.go:1954-1956` at the pin `673da07c8` calls `applyConfChange` with `shouldApplyV3` false)
  over what Go does with one (corrected 2026-11-06: an earlier brief said such a replay is applied to
  raft and the v2 membership, which is false): at the pin a replayed conf change (`shouldApplyV3` false) is applied neither to raft nor to the
  membership: `ValidateConfigurationChange` returns `nil` at once (`membership/cluster.go:306-308`),
  `ApplyConfChange` runs only `if shouldApplyV3` (`server.go:2053-2059`, so raft is not told and
  `ep.confState` is unchanged), `AddMember`/`RemoveMember` only log (`membership/cluster.go:402-424`);
  what does run is `beHooks.SetConfState` (of the unchanged `ep.confState`), the transport's
  `AddPeer`/`RemovePeer`/`UpdatePeer` and `w.Trigger` (the Freeze 1 review's F6; not a Go bug), and, for
  a removal of the member itself, the server's stop: `removedSelf = true` at `v3 = false` too
  (`server.go:2087-2089`), so `apply` returns `shouldStop` and `applyEntries` stops the server
  (`:1236-1237`); R2d''s `v3 = false` case of `applyConfChange.spec` must model it (the Freeze 1b
  review's N5; not a Go bug: a replayed self-removal was valid when first applied, or the member was
  already removed).
  **Re-check of the discharge plan (2026-11-06): it still holds, at a cost not listed before.**
  Nothing changes raft's or the membership's state, so `run`'s and `srvRest`'s rows are kept by such a
  replay; but `applyConfChange.spec` has no `v3 = false` case (it requires `dv = some n → v3 = true`,
  `EtcdServer__applyConfChange.lean:78-81`): R2d' adds one (the conf state and members unchanged, the
  transport's peers by `ccPeersAfter`'s `v3 = false` case, `SetConfState` of the old conf state), a
  statement change for R2d''s Scope, with `dvOk`'s window form; **not** through `bootLen ≤ σ.b` (which
  would rule out only the bootstrap log's conf entries, not a later one in `(σ.b, i]`). Until then
  the three window specs take `winNoConf W` as a premise (the Freeze 1 review's F1).
- **R2e**: the restart's closed result. HS2's static-cluster premise goes in R2e's Scope (Q14 caveat
  (ii)): the restarted storage's conf state is the backend's at `i` (`bootstrap.go:107-115`), which
  `confStateIs` the membership at the WAL snapshot's index only in a static cluster.
  (2026-11-06, Q20's decision 3, then superseded the same day by the held items' decision 2,
  decided by etcd-grove-82 under the user's delegation (user offline), 2026-11-06, pending the user's review) HS2's `i ≤ σ.commit` is no longer R2e's: R2d keeps `i ≤ σ.commit` in the stop's image
  (the Q16-3 review's finding 2 reverted), and its weakening moves to **R2s** with the trusted
  contract's (below, "R2d Draft, round 3").
  (2026-11-06, the Q16-3 review's item 2, decided by etcd-grove-82 under the user's delegation,
  pending the user's review) **R2e's closed theorem carries neither `winNoConf` nor
  `winNoMergedSend`**: it waits for R2d' (which discharges the first) and R2s (the second). The order
  is R2d, R2d', R2s, R2e.

**The window form (Q13 (a)), DRAFT; stopped for review before `run`'s proof.**
- `ApplyWindow.lean`: the window's vocabulary over the pending replays `W` and the done ones `D`
  (`winGhost`, `winNew`, `winRest`, `winDone`, `winAgree`, `winOk`; `kvBatchW`, `restReplay`,
  `srvRestW`). Each reduces to the no-window one *by definition* at `W = D = []`.
- `apply.spec`, `applyEntries.specBatch`, `applyAll.specBatch` restated over it (one spec per
  function; `kvBatch` is `kvBatchW` at `[]`). The ghost rows (applied index, ghost log, `srvRest`,
  `kvBatch`) at `winGhost`/`A ++ winNew W …`; Go's rows unchanged.
- `ApplyWindowLaws.lean`: today's texts kept as `…NoWin`, and the laws `apply.spec_noWin`,
  `applyEntries.specBatch_noWin`, `applyAll.specBatch_noWin` (instantiation at `winOk_nil`, glue).
  The first-start callers go through them: `run_job_body`, `ModeSpecs`' `apply.spec_off`/`spec_on`,
  `applyAll`'s call of `applyEntries`. No frozen or exported statement changes (`run.spec`,
  `start`/`Start.spec`, `isServerRun*`/`isServerBuilt*`, `NewServer.specG` untouched).
- The three window forms' `wp_proof`s are `sorry -- DRAFT (R2d window form; proof after the Freeze)`;
  the old proofs stay, proving the `…NoWin` texts (`wp_proofNoWin`, `wp_proofBatchNoWin`).
- The `applied_jump` reuse (condition 3) is for `run`'s proof: the window's start is the snapshot
  install's jump of the ghost index, `winGhost` its only notion of replay.

**Q14 (a), DRAFT, all proved.** `walSnapCert cl σ` (`InvWal.lean`: the records at index `0`, or
their snapshot, of no data at their base, valid) is carried in the WAL's durability invariant
(`walAsViewed`, `rnDurInv` over the cluster), supplied by the two `SaveSnap` AUs (the apply thread's
from `wp_srv_createSnapshot`'s certificate, the received one from raft's `rnReadySnap` through
`srv_snapshotValid_record`), returned by `rnDur_take`, through `rnStopImage`, `rn_esc_take`,
`raftNode.stop.spec` and `stopCleanupImage.spec` into `srvDiskImage` (a frozen R2c predicate: one
conjunct added). No `walFiles` axiom; the trust base unchanged.
- **Caveat (i) settled:** a received snapshot's raft data is nil. The cluster's snapshot registry
  now holds only nil-data snapshots (`srvSnapsReg`, in `srvClusterOk`: the server registers only
  `CreateSnapshot(…, nil)`'s, `server.go:2137`; the merged snapshot's `Data` is unset,
  `snapshot_merge.go:43-50`), so a valid snapshot has nil data (`srv_snapshotValid_dataNil`) and is its
  WAL record's (`srv_snapshotValid_record`).
- One raft API addition: `snapMade_timeless` (so `snapshotValid` is timeless at a client).

**Scope amendment 2 (2026-11-06, Q16; decided by etcd-grove-82 under the user's delegation, user
offline, pending the user's review).** The hard probe on the window form (`applyAll.wp_proofBatch`)
found: (1) the window form's `lastTermIs A at0` cannot hold at a restart (Go's `ep.appliedt` is the
WAL snapshot's term, `server.go:812-813`): now `lastTermIs (A.take (uint.nat ai)) at0`; (2) the local
snapshot after a window batch is at Go's applied log `take ai A ++ unapplied ai ms` (a proof matter,
a list lemma); (3) (**superseded 2026-11-06 by R2s**, "R2d Draft, round 3" below) a merged snapshot sent in a window (`server.go:1008-1023` at the pin `673da07c8`; Go merges a
`MsgSnap` only at the batch's raft term and at or below `ep.appliedi`, `m.GetTerm() == apply.raftTerm
&& m.GetSnapshot().GetMetadata().GetIndex() <= ep.appliedi`, `:1018`, calling
`createMergedSnapshotMessage`, `snapshot_merge.go:32`, at `:1019`) carries an image at the
backend's consistent index `j` above its metadata index: the network's image certificate
(`srvNet`'s `img`) becomes "an image at some `j ≥ i`", and the receiver's install (`applied_jump`,
`applyAll.specSnap`/`specSnapM`) gains the same replay window (Q13's `ApplyWindow`), so one notion of
window covers restart and install (design: `/shared/tmp/r2d-merged-design.md`, to be moved into this
plan when drafted). This is R2d's last widening: another Scope-level gap stops with a proposal to move
it to R2d' or a new stage. **Estimate: R2d now about 5-7 weeks.**

**The review round's edits (2026-11-06; F1-F8 and Q16 (1) decided by etcd-grove-82 under the user's
delegation, pending the user's review; `questions.md` Q17).** Done on `r2d`: Q16 (1) and F2
(`cfdb33f8f1`); F6 raft's client laws `snapshotValid_timeless`, `ownSnapsMade_snapshotValid_data`
(the server no longer unfolds `snapshotValid`); F7 the WAL's slot `wal.stopImage` in `srvDiskImage`
(the static-cluster margin in its docstring); F8 docstrings; F1 `winNoConf` (above, the R2d' list);
F4 `applyAll.specBatch`'s frozen terms over Go's applied log (`take ai A ++ unapplied ai ms`): raft
freezes entries only through Go's end, a restarted `MemoryStorage` only up to its snapshot.
- **Post-Freeze sub-step: the receive proofs from `i` to `j`** (Q16 (3)): `ApplyAllSnap.lean` (250
  lines), `ApplyAllSnapOn.lean` (550), `SnapRecvFacts` generalized to the image at the consistent
  index `j ≥ i` (the install at `j`: `image_restoreRes`, `dbImage_of_srvImage`, `applied_jump` to `j`;
  Go's rows at `i`), about 800 lines, its own sub-step after the Freeze.
- (**Superseded 2026-11-06 by R2s**, "R2d Draft, round 3" below.) **Q16 (3) stopped before its Lean edits (Q18, open).** `srvSnapRO` keys the snapshot directory by
  `srvImageM` itself (`SnapRO.lean:452`), so the network certificate's change reaches every receive
  proof at once, and `run`'s three snapshot-job lemmas (`EtcdServer__run.lean:299, 506, 683`) would
  receive a window post that `run`'s invariant (R2d-5's window) cannot take yet: a 5th DRAFT sorry, or
  R2d-5 brought forward. Proposed cut: a sub-step R2d-3m after R2d-5 doing the certificate, the
  receive window and `run`'s snapshot job together.

### R2d Draft, round 3: R2s, the Q16-3 review, R2d-2's statements (2026-11-06, branch `r2d`)

*Superseded in part (2026-11-06, "R2d cut (Q21)" below): the window-form apply chain, `winNoConf`, `winNoMergedSend` (and its hub conjunct), Q19, F2, F4 and finding 6 moved from R2d to R2d'; the restage's R2d list is now the cut's.*
*Reorganized (2026-11-06) by "R2d' Scope (approved 2026-11-06)" below: its R2d' contents are now that section's R2d'a/R2d'b items; where they differ, that section holds.*

**R2s, "snapshots across windows"** (the Q16-3 review's item 1, decided by etcd-grove-82 under the
user's delegation, pending the user's review; supersedes Q16 (3) and Q18's R2d-3m; `notes/decisions.md`,
"R2s: snapshots across windows"). A new stage, ordered **R2d, R2d', R2s, R2e**. It carries:
- the KV ghost reset at an install (the monotone applied index at Go's index, the KV ghost
  `appliedLogAt`/`kvApplied` the backend's, reset at an install to the image's committed prefix, which
  may be shorter; `srvSnapRm` keyed by Go's applied index);
- the raft fact "a snapshot's index is above the receiver's commit" (a raft API change, decided at
  R2s's Scope);
- `applySnapshot.specSnapM` and `srvSnapApplied*` restated (their `ciEff ≤ sv.Index` and `A <+: A'`);
- Q16 (3)'s certificate (the merged image at the sender's consistent index) and `srvSnapRO`'s key;
- the discharge of `winNoMergedSend` (below).

*Its motivating case* (the review's F1; Go is correct, nothing for `issues/`): leader L1 in a restart
window (Go 60, backend and ghost 100) sends F a merged snapshot at 60 with its image at 100; F installs
it (raft commit 60, Go 60, ghost 100). Leadership moves to L2, applied to 70, its log compacted past
61; L2 probes F, finds it behind its first index and sends a merged snapshot at 70, image at 70. F's
raft accepts it (above its commit 60, `raft.go:1877`), Go accepts it (above `ep.appliedi` 60,
`server.go:1051` at the pin `673da07c8`), F's backend goes from 100 back to 70 and Go re-applies 71..100 with v3. The ghost
cannot follow: `applied_jump` moves a monotone counter forward only (`InvRequest.lean:2312`), and the
snapshot directory's removal fact is keyed by the ghost index (`SnapRO.lean:345,358`).

**Assumptions R2d carries** (`questions.md`, "Assumptions R2d carries for R2d'/R2s"): `winNoConf`
(R2d' discharges it) and `winNoMergedSend` (R2s discharges it). `winNoMergedSend γ s R rt`
(`ApplyWindow.lean`, narrowed by the Freeze 1 review's F2): with a window left after the batch
(`R ≠ []`), every wholly owned message member `id` (the server's `memberID`) sent is not a `MsgSnap`
at the batch's raft term `rt`; `applyAll.specBatch`'s premise; trivial with no window left
(`winNoMergedSend_nil`). What it asserts (corrected 2026-11-06, the Freeze 1b review's N1): `sentMsg`
is persistent and keyed by the member id, not the incarnation, so in practice member `id` has never,
in any incarnation, sent a `MsgSnap` at `rt`. R2d' supplies it per batch from a persistent assumption
of the restart's starting point: no `MsgSnap` from this member from its restart term on, nor at that
term before the stop. Its cost: it does not hold of every Go execution: a leader in its window does
send one, and a leader at term `T` that sent a snapshot, stopped without a leadership transfer and
restarted at term `T` with a window violates it though Go merges nothing in the window. `applyAll.wp_proofBatch`'s merged-send branch at a pending window is refuted by it: the
window form's proof is sorry-free.

**The review's other items, done on `r2d`** (`questions.md`, the Freeze list): item 4, Q16 (3)'s
sender-side statements are not in R2d (none is in the Lean; the receive specs as on lean); finding 2,
`wal.stopImage` kept only `σ.b ≤ i` (ae43b933dd; **reverted** the same day, the held items' decision
2: R2d keeps `i ≤ σ.commit`; the weakening is R2s's, below); finding 6,
`applyAll.specBatch`'s `≤ n` over Go's applied log.

**R2d-2's statements: drafted, not in the hub predicates; the probe extension stops at `Hsnap`
(`questions.md` Q20).** In `RunWindow.lean` (DRAFT, for Freeze 2): `srvRestartPt P A₀` (`P <+: A₀`,
`winNoConf` of the window), `srvCMW` (`srvCM` after `P`), `srvRestartAt` (`applyStartC` at `A₀`, Go's
rows at `winGhost ai₀ P`, with `winNoMergedSend`), `applyResCW` (`applyResC` in a restart's window,
Go's index `ai₀ + |P ++ A|` below the ghost one), each today's at a first start by a law
(`srvCMW_nil`, `srvRestartAt_nil`, `applyResCW_nil`). The probe's glue, all proved: `applyResCW_start`
(the loop's resources at a restart's start, from `srvRestartAt` and Go's fields) and
`applyResCW_firstBatch` (the first batch's `winOk`, through `run_firstBatch_window`). It stops at
three premises of `applyResCW_start` that `isServerRunC` cannot give at a restart, all a first
start's `Hsnap` (`rnSnapOnce … ai₀ at₀`: the storage's snapshot at `ai₀ = 0`, `memSnapNone`), which
is not in Q12's list. Proposed cut: `rnSnapOnce` gains the handed log `P` (index `winGhost ai₀ P`,
term `P`'s, the conf state at `A₀`, the restarted storage's token: R2d-6's `memStorRestarted`),
today's at `P = []`; the hub edit (with `%HEr`, `Hstart`/`Happ`, `Hsnap`) after R2d-6, and with
R2d-5's `run` proof (else every first-start closed theorem reaches `run`'s DRAFT restart branch).
R2d-2's statements move to Freeze 2.

**Sorries on `r2d`** (all `-- DRAFT`): `apply.wp_proof`'s and `applyEntries.wp_proofBatch`'s window
forms. `applyAll.wp_proofBatch` and `RunWindow.lean` have none.

**The restage (2026-11-06, Q20, decided by etcd-grove-82 under the user's delegation, user offline,
pending the user's review; supersedes the R2d / R2d' contents of "R2d Draft, round 2" and the Freeze
split of Q18; `notes/decisions.md`, "R2d restaged: the restart's prerequisites").**
- **R2d = the restart's prerequisites.** The window-form apply chain (Q13, Q19, Q17 F2/F4, the Q16-3
  review's finding 6); Q14's stop certificate with `srvDiskImage`/`wal.stopImage` (its slot form, F7, with
  `i ≤ σ.commit`); `setAppliedIndex.spec`'s replay case; `kvCongr`/`restartNames` (Q8 (a)); raft's
  additive laws
  (`snapMade_timeless`, `snapshotValid_timeless`, `ownSnapsMade_snapshotValid_data`); the two
  assumptions `winNoConf` and `winNoMergedSend` with their laws. One Freeze (no Freeze 2). R2d lands
  once `apply.wp_proof`'s and `applyEntries.wp_proofBatch`'s window forms are proved. **Estimate:
  1-2 weeks (est.)**, mostly those two proofs.
- **R2d' = `run` and `NewServer` at a restart**: R2d-2's hub edit (`%HEr`, `Hstart`/`Happ`, and
  `Hsnap`'s restart form, Q20), R2d-5 (`run`'s proof over the window), R2d-6 (`memStorRestarted`,
  `newRaftNode`'s `RestartNode` path), R2d-7 (`NewServer.specG`'s boot argument), B1 (`NewStore`'s
  restoring case), the `winNoConf` discharge, and **HS1** (moved from R2d, below). **Estimate: 5-7
  weeks (est.)**.
- Then **R2s** (snapshots across windows, discharging `winNoMergedSend`), then **R2e** (the closed
  result).
- **`RunWindow.lean`** (R2d''s starting point, imported by nothing, sorry-free): not worth landing
  with R2d. Its R2d-2 definitions (`srvRestartAt`, `applyResCW`) will be restated once `Hsnap`'s
  restart form is decided (the glue lemma `applyResCW_start` takes exactly what that form must give),
  and nothing in R2d uses them or `run_firstBatch_window`; landing them would freeze-review dead
  DRAFT vocabulary. Recommendation: drop the file from R2d's landing commit range (or move it to an
  `r2d-prime` branch) and carry it into R2d'. **Moved (2026-11-06):** branch `r2d-prime` (made at
  `r2d`'s head before the deletion, so it has `RunWindow.lean`, using the public window list laws of
  `ApplyWindow.lean`) is R2d''s starting point; `r2d` deletes the file in its own commit.

**The held items (2026-11-06, decided by etcd-grove-82 under the user's delegation (user offline), 2026-11-06, pending the user's review).**
- **`winNoMergedSend` narrowed** (the Freeze 1 review's F2; 82 approves, as hub-plan owner, exposing the
  member's id in `isServerApplyAll`): design in `/shared/tmp/r2d-wnms-design.md`, **approved by 82 as
  designed and applied**: while a window remains after this batch, this member does not merge a
  MsgSnap of the batch's raft term. A
  one-shot premise of `applyAll.specBatch` over the window left after the batch
  (`winRest W (unapplied ai ms)`): the batch takes from `msgSnapC` no `MsgSnap` of this member at the
  batch's raft term; `isServerApplyAll`/`srvApplyAllBuilt` gain `srvMemberIDAddr s ↦□ γm.id`,
  `NewServer`'s proof supplying it. R2d' supplies the premise per batch from the restart's starting
  point (`run`'s loop over batches, each of its own term). (Corrected 2026-11-06, the Freeze 1b
  review's N1: `sentMsg` is keyed by the member id, not the incarnation, so the premise says member
  `id` never sent a `MsgSnap` at `rt` in any incarnation; R2d' supplies it from the assumption that
  this member sends no `MsgSnap` from its restart term on, nor sent one at that term before the stop;
  "Assumptions R2d carries" above.)
- **The stop's `i ≤ σ.commit` stays in R2d** (the Q16-3 review's finding 2 reverted; `wal.stopImage`'s
  slot form and its elimination law kept). **R2s** carries its weakening, together with the trusted
  `bootstrapRestartContract`'s premise `uint.nat i ≤ σ.commit` (a trust change, with its `axiom`-skill
  attack): a member that stops inside an install window (it installed a merged snapshot whose image is
  at the sender's consistent index above the snapshot's index, R2s's motivating case) leaves its
  backend's consistent index above its WAL's HardState commit, and etcd itself handles that case
  (`bootstrap.go:613-621`, `consistent_index > Commit`). R2d excludes it: no install from a window
  sender (`winNoMergedSend`). The stop's configuration point then over `[σ.b, σ.commit]` (`∃ p,
  confAt cl p m`, the form drafted in ae43b933dd).
- **HS1 moves to R2d'** (with its consumer, `NewServer`'s restart branch through `authStoreKit`). The
  widening is reverted on `r2d` so R2d lands with no trust change; the approval (HS1 (a)) and the
  attack carry over. To re-apply in R2d': in `auth.NewAuthStore.spec`'s precondition
  `(r.lookup go!"auth").getD ∅ = ∅` → `((r.lookup go!"auth").getD ∅ = ∅ ∨ (r.lookup go!"auth").getD ∅ =
  authBoot)`, users'/roles' unchanged, and `authStoreKit_off`'s `Hr` → `Or.inl Hr.1, Hr.2`
  (`AuthSrv.lean:317`); the patch is `/shared/tmp/r2d-hs1.patch` (from bba7cb04e4). The docstring's
  attack, verbatim: "**Two cases, one end state.** (1) A first start: the auth bucket empty (`∅`), as
  above: `enabled` false (no `authEnabled` key), the revision `0`, so `commitRevision` runs (in memory
  `0 → 1`, the bucket's `authRevision` put to `1`): the bucket ends at `authBoot`. (2) A restart: the
  auth bucket at `authBoot` (what case (1) left; the image's, `bkRestAt_boot`): `CreateAuthBuckets` is
  a no-op on the existing buckets (schema's `UnsafeCreateBucket` is bbolt's `CreateBucketIfNotExists`,
  `backend/batch_tx.go:136-145`, which returns an existing bucket and writes nothing,
  `bbolt@v1.5.0/bucket.go:230-250`; its `pending++` only schedules a commit), the write-backs are the
  same two; `UnsafeReadAuthEnabled` reads no `authEnabled` key in `authBoot`: false;
  `UnsafeReadAuthRevision` reads `authRevision`, one value, big-endian `1` (`schema/auth.go:137-144`):
  the in-memory revision `1`, as case (1)'s after its commit; `Revision() ≠ 0`, so `commitRevision` is
  skipped and the bucket stays `authBoot`; `refreshRangePermCache` reads `authUsers` (empty in both
  cases: no user, so `authRoles`, read only per user, is not read; `range_perm_cache.go:131-150`). So
  both cases end with the store disabled at revision `1` and the auth buckets at `authBoot`/`∅`/`∅`:
  the post is the same. Not covered (excluded by the premise): an `authEnabled` key, a revision other
  than `0` or `1`, any user or role." The collections resting on `NewAuthStore` (they will rest on the
  stronger claim when it is re-applied): `putget`, `putget3`, `cachekv`, `compactkv`, `leasekv`,
  `leasecatchup`, `leaseexpiry`, `linkv3p`, `k8setcd3`, `k8scompactor` (`etc/tcb-collections/`).
  Nothing on `r2d` uses the widening (only `authStoreKit_off`'s `Or.inl`); `RunWindow.lean` goes to
  `r2d-prime`.
- **`winNoConf`'s R2d' discharge, re-checked** against `server.go:2053-2059` and
  `membership/cluster.go:306-308`: a replayed conf change is neither validated nor applied to raft, and
  the membership only logs (`cluster.go:402-424`). What changes: the discharge is not "applyConfChange's
  v2-only case" of today's spec (it has none: `dv = some n → v3 = true`); R2d' adds a `v3 = false` case
  to `applyConfChange.spec` (raft, `ep.confState` and the members unchanged; `SetConfState` of the old
  conf state; the transport's peers by `ccPeersAfter`'s `v3 = false` case; `w.Trigger`), a statement
  change for R2d''s Scope. Until then the three window specs take `winNoConf W` (the Freeze 1 review's
  F1).

### R2d cut (Q21): the window-form apply chain moves to R2d' (2026-11-06, branch `r2d`)

*Reorganized (2026-11-06) by "R2d' Scope (approved 2026-11-06)" below: its "To R2d'" list and its two constraints are met there by the restart point over Go's log (the `W`/`D` lists dropped), the per-entry `v3 = false` cases and `winNoConf`'s discharge.*

**Decided by etcd-grove-82 under the user's delegation (user offline), 2026-11-06, pending the user's
review** (Q21 (b); `notes/decisions.md`, "R2d cut: the window-form apply chain moves to R2d'"). The
post-Freeze proof round found `apply.wp_proof`'s and `applyEntries.wp_proofBatch`'s window forms
unprovable as frozen. R2d lands without the window form:
- **R2d keeps** Q14's WAL certificate chain (`walSnapCert`, `rnDurInv`/`walAsViewed` over `cl`, the
  `rnDur_*` laws, `wal.stopImage` with `_intro`/`_elim`, `srvDiskImage`'s slot, the stop chain's
  `walSnapCert`, `isRaftNode`/`rnWalTokA`'s `rnDurInv γ.node.cl …`), `srvSnapsReg`,
  `setAppliedIndex.spec`'s replay case, `kvCongr`/`restartNames`, raft's three additive laws and
  `rnEnvOk_logInv`. No DRAFT `sorry`, no trust change, no hub change.
- **Back to lean's text:** `apply.spec`, `applyEntries.specBatch`, `applyAll.specBatch` and their
  proofs, `isServerApplyAll`/`srvApplyAllBuilt`, `ModeSpecs`, `run_job_body`, `SDRun`;
  `ApplyWindow.lean`/`ApplyWindowLaws.lean` deleted. (`apply`'s proof file keeps only the
  specialisation of `setAppliedIndex.spec` to `rep = false`.)
- **To R2d'** (tags `r2d-freeze1`, `r2d-window-full`; branch `r2d-prime`): the window vocabulary,
  `winNoConf`, `winNoMergedSend` and its member-id conjunct, Q19's `dvOk` index, F2, F4, finding 6
  and Q16 (1)'s `lastTermIs`.

**Constraints R2d''s window design must meet** (Q21's two findings, checked against Go at the pin
`673da07c8`):
1. **A replayed normal entry needs its own triple.** In Go every replayed normal entry goes through
   `applyEntryNormal(e, ApplyV2storeOnly)` (`server.go:1938-1949`), which runs `apply.Apply` with
   `shouldApplyV3` false (`:1975-2000`): it updates v2 member attributes, and on an empty entry it
   notifies `firstCommitInTerm` and may promote the lessor. Today's `applyEntryNormal.spec` cannot
   be used for it: its pre needs `m.index = v + 1` at the ghost index `v` (`srvAppliedOwn γr v`, half
   of a monotone counter), and its post grows the ghost log (`A ++ [m]`); in a window the ghost
   index is above `m.index` and the ghost log must stay unchanged. R2d' needs a replay case of
   `applyEntryNormal.spec` (ghost and KV unchanged; the rest model stepped by `restEntry` at the
   ghost index, `restReplay`'s step), a new statement, provable from the existing `v3 = false`
   branch.
2. **Closing the window needs an identity that is false for conf changes.** When the window closes
   (`winRest W ms = []`) or nothing is applied, the post needs `restReplay γr A D = restModel …
   (pre ++ A)`. With a conf change in the replayed `D` this is false: `D = [attr(X,a), add X]`
   (in `restModel` the attribute update of a not-yet-member is a no-op; in `restReplay`, over the
   members already added, it sets X's attributes). And `winOk` allowed `W = []` with `D ≠ []`. The
   design must exclude conf changes over all of `D ++ W` (or model them), tie `W = []` to `D = []`
   (or carry `D` in a `winDone` that keeps it), and prove the identity for normal entries (last writer
   wins; `restSetVersion false` the identity).

**The lesson for R2d''s Scope.** The window failed three probes when designed from the apply chain
upward. Design it from `run`'s window downward, with a probe through `run`'s restart batch before any
spec is frozen.

### R2d' Scope (approved 2026-11-06)

**The design and the hard stops H1-H10 are decided by etcd-grove-82 under the user's delegation
(user offline), 2026-11-06, pending the user's review** (the worktree's `questions.md`, "R2d' Scope";
the plan in full, with every citation: `/shared/tmp/r2d-prime-scope.md`; `notes/decisions.md`, "R2d':
the restart window as a restart point over Go's log"). This section reorganizes the earlier R2d'
contents of this plan ("R2d Draft, round 2"'s R2d' bullets, the restage's R2d' list in "R2d Draft,
round 3", the "To R2d'" list and the constraints of "R2d cut (Q21)"): where they differ, this section
holds. Go is cited at the etcd pin `673da07c8`, raft at `565c2bd`.

**The design: from `run` downward** (the lesson of Q21: three probes failed when the window was
designed from the apply chain upward).
- `run`'s loop is indexed by **Go's log** `G`, the log raft handed (as `RunWindow.lean` on branch
  `r2d-prime` already is). Every callee down the chain takes Go's log as its log.
- A restart adds one constant per incarnation, the **restart point** `rp = ⟨b, A₀⟩`: Go's start
  index `σ.b` (the WAL snapshot's) and the backend's ghost log `A₀` through the consistent index `i`.
- The ghost log is derived: `ghostOf rp G = G ++ A₀.drop |G|`; so are the pending replays
  (`A₀.drop |G|`) and the done ones (`G.drop b`, while pending). At a first start `rp = ⟨0, []⟩` and
  `ghostOf rp G = G`: a law gives today's text.
- Go's rows (`ep.appliedi`/`appliedt`, `loopOk`, `srvSnapState`, raft's rows of `run_job_body`) keep
  lean's text; only the ghost rows (`srvAppliedOwn`, `appliedLogAt`, `kvRunM`, `srvApRes`, `epCsAt`,
  `ciJ`) move to `ghostOf`; the rest row is `srvRestR` (`restReplay A₀ (G.drop b)` while the window is
  pending, `srvRest` after); the driver's view is over the ghost (finding 1).
- `winOk`, `winAgree`, `W`, `D`, `winDone` and the F2 premise go away (`r2d-window-full`'s lists):
  what they stated follows from the committed log's uniqueness and `ciJ` (`ciEff = |Γ|` pins every
  replay at or below the consistent index). Q16 (1), F4 and finding 6 stop being changes: they are
  lean's text with `A` read as Go's log.
- **Per-entry replay**, at Go's index with the ghost unchanged: a `v3 = false` case of
  `applyEntryNormal.spec` (no ghost rows; the rest resource stepped by `restEntry`, `srvApplyKVM` by
  `entryStep m false`) and of `applyConfChange.spec` (`dv = some n → (v3 = true → srvCCPre …)`; at
  `v3 = false` the view unchanged and `csl = cs`), with R2d's `setAppliedIndex` `rep` case. `apply`,
  `applyEntries` and `applyAll` keep one spec each, because a batch can straddle `i` (raft's
  `MaxCommittedSizePerReady` splits the first committed entries; `bootstrap.go:580-599`).
- **`winNoConf` is discharged, not carried**: by `applyConfChange`'s `v3 = false` case and the pure
  lemma `restReplay_close` (replaying any suffix of the committed log v2-only on `restModel L` gives
  `restModel L`), from the static-membership facts every closed theorem already rests on (`ccApplyOk`,
  `attrLogOk`, the boot prefix, `membersDecode_restModel`'s argument). Q21's counterexample
  `D = [attr(X,a), add X]` is not a log those facts allow. `srvRestartPt` loses its `winNoConf`
  conjunct.

**Scope items.**

| # | Item | Kind | Est. |
|---|---|---|---|
| A1 | Window vocabulary: `RestartPt ⟨b, A₀⟩`, `ghostOf`, `srvRestR`, the KV facts over new entries; the first-start laws (replaces `r2d-window-full`'s `ApplyWindow.lean` lists) | new | 2-3 d (est.) |
| A2 | `restReplay_close` | new (pure) | 3-5 d (est.) |
| A3 | `applyEntryNormal.spec`'s `v3 = false` case (the `v3 = true` text unchanged) | frozen, internal | 2-3 d (est.) |
| A4 | `applyConfChange.spec`'s `v3 = false` case (with A2, discharges `winNoConf`) | frozen, internal | 3-4 d (est.) |
| A5 | `apply.spec`, `applyEntries.specBatch`, `applyAll.specBatch` over `(rp, G)`; new premises `rp.b ≤ |G|`, `srvRLogLb γ A₀`; `dvOk` at `|ghostOf rp G| + 1` (Q19) | frozen, internal (lean's text at `⟨0, []⟩` by a law) | statements 2 d; proofs `apply` 5-7 d, `applyEntries` 2 d, `applyAll` 3-5 d (est.) |
| A6 | The driver's view over the ghost (finding 1, H4 V1): `dvView`/`dvRes`/the `notifyc` payload, the raft loop's `rnCfgAt` and the `rnApR_dv` bridge with `A₀` | hub | 4-6 d (est.) |
| A7 | `winNoMergedSend` as frozen at `r2d-freeze1`, with the `isServerApplyAll`/`srvApplyAllBuilt` member-id conjunct; its supply at `run`'s restart branch (H6: the token wand) | hub; restart-only assumption | 1-2 d (est.) |
| A8 | An install inside a restart window (finding 2): `winInstallAbove` (H5 (a)) | restart-only assumption | 1 d (est.) |
| A9 | R2d-2's hub edit: `isServerRunC`/`isServerBuiltC`'s `%HEr` (`γn.pre = []` → `P <+: A₀` with `rp`), `Hsnap`'s restart form (`rnSnapOnce` at `|P|`, `P`'s term, `epCsVoters`, the storage's snapshot token named by raft's `MemoryStorage` API), `Hstart` = `srvRestartAt` | hub | 3-5 d (est.) |
| A10 | R2d-5: `run.wp_proof`'s restart branch (`applyResR`, its start, normal and snapshot jobs in a window, the merged-send supply, the stop at a restart: `σ'.b ≤ Go ≤ i' ≤ σ'.commit`); `run.spec`'s text unchanged, its docstring's "Scope: a first start" updated | frozen (scope widens through `isServerRunC`) | 2-3 wk (est.) |
| A11 | Freeze package, a fresh `spec-reviewer` round | — | 3-4 d (est.) |

**R2d'a (A1-A11): 5-7 weeks (est.), the probe included.** It lands with no producer of the restart
form (`NewServer` still builds a first start through the laws); the first-start closed theorems are
unchanged and reach no DRAFT `sorry` (the hub edit lands with A10's proof, Q20's condition); the
trust base is unchanged but for A7/A8, which no closed theorem reaches.

**R2d'b, `NewServer` at a restart: not started: after the user's review or R2d'a's Freeze, 82
decides** (H8; the estimate went from 5-7 weeks for all of R2d' to 10-14 (est.)).

| # | Item | Kind | Est. |
|---|---|---|---|
| B1 | R2d-6: `memStorRestarted` defined over `walSnapCert`; `newRaftNode`'s `RestartNode` path at `a = i`, `nodeConfig ⟨i, m⟩` | new; trusted `bootOkR` text over it | 1 wk (est.) |
| B2 | Q15's B1: `mvcc.lateWB`'s unregistered arm `pvckEmpty` → `pvckOwn`; `lateWBR` merged away (H7 (a): the trusted claim weakens; the `axiom` skill before the Freeze) | trusted | 3-5 d (est.) |
| B3 | `mvcc.New`/`NewStore`'s restoring case | frozen | 1.5-2 wk (est.) |
| B4 | HS1 re-applied (`/shared/tmp/r2d-hs1.patch`) | trusted | 0.5 d (est.) |
| B5 | R2d-7: `NewServer.specG`'s restart branch builds `isServerBuiltC`'s restart form from `bootOkR`; H10's check first | hub | 2-3 wk (est.) |
| B6 | R2d-8: etcdstart over both boots | frozen | 0.5-1 wk (est.) |
| B7 | Freeze, review | — | 3 d (est.) |

R2d'b: 5-7 weeks (est.); R2d' in all 10-14 weeks (est.). What the earlier 5-7 did not count: the
per-entry replay specs (A3, A4), the view at a restart (A6), the install in a window (A8),
`NewStore`'s restoring proof at its size (B3) and the probe. H10 (before R2d'b's Freeze): whether
`cl.Recover`'s in-memory members equal `restModel A₀`'s `mem`, attributes included; if the trusted
restart contract does not already say so, a JSON round-trip fact for `MemberM` is new trust, a hard
stop.

**The probe (H9, first; 7-10 days (est.)).** A restarted member's **first batch, straddling `i`**:
its replayed part holds a normal entry with a `ClusterMemberAttrSet`, an empty entry and a boot
`AddNode` (a restart with `σ.b < bootLen ≤ i`); entry `i` closes the window; one new entry follows.
Proved, top to bottom:
1. `restReplay_close` (pure);
2. `apply.wp_proof`'s window form, over the drafted `v3 = false` cases of `applyEntryNormal.spec` and
   `applyConfChange.spec` taken as hypotheses;
3. `applyEntries.wp_proofBatch`'s window form;
4. `run_job_bodyR` (the restart form of `run_job_body`) over the drafted `applyAll.specBatch`, for two
   consecutive batches, this one and one after the window: `applyResR` re-established in both arms,
   the second reducing to the first-start text;
5. `applyResR_start` (`applyResCW_start` in the `rp` form), over a drafted `Hsnap` restart form;
6. the view's round trip for the replayed conf entry, over a drafted ghost-indexed `rnCfgAt`.

Pass: all sorry-free, with the two leaf specs and `applyAll.specBatch` as hypotheses only. Left out:
`applyAll.wp_proofBatch` (adapted after), snapshot jobs in a window, the stop at a restart,
`NewServer`. **H9's rule: on a gap, stop with a proposal, and freeze nothing.**

**Two new findings.**
1. **The driver's view at a restart.** `RestartNode`'s view is `⟨a, m⟩` with `a ∈ [max σ.b Applied,
   σ.commit]`; `a` must be `i` (Go skips every conf entry in `(σ.b, i]`, and `ApplyConfChange` may
   skip only conf entries below the view, `skippedIn_noConf`). Then `srvCfgOk` over Go's log is false
   while `|G| < i`, and the raft loop's `rnCfgAt` bridges to the apply side by `rnApR_dv`/`rnApGive_dv`,
   which need `γn.pre = γs.pre` (`InvRaftLoop.lean:218-240`), false at a restart. So the view is
   stated over the ghost log on both sides, `A₀` in the raft loop's restart data (A6; H4 V1, approved
   by 82 as hub-plan owner on condition that the first-start statements and closed theorems stay
   unchanged).
2. **An install inside a restart window** needs the snapshot's index above the *ghost* index `i`
   (the receive proofs jump the monotone ghost, `applied_jump`). Raft gives it (`restore` refuses
   `index <= committed`, `raft.go:1876-1880`, and `i ≤ σ.commit`), but no Lean statement does; Go
   checks only `sIdx > ep.appliedi` (`server.go:1051-1059`). `run`'s snapshot jobs can run while the
   window is pending (a split first batch, a snapshot between). A8 (H5 (a)).

**The carried restart-only assumptions**, with their honest costs (R2s discharges both; R2e carries
neither, nor `winNoConf`):
- **A7, `winNoMergedSend`'s supply** (H6: a persistent wand guarded by an exclusive "window pending"
  token the apply thread holds until the window closes: while it is held, member `id` has no
  `MsgSnap` at a term `≥ T₀`). Cost, as N1's honest reading: it excludes runs where member `id` has a
  `MsgSnap` at a term `≥ T₀` while the window is pending, including an earlier incarnation's sends at
  the restart term (`sentMsg` is incarnation-blind). No wider than the frozen premise.
- **A8, `winInstallAbove`**: a snapshot raft hands this incarnation is above `i`. True of every Go
  execution (`raft.go:1877` with `i ≤ σ.commit`); its cost is that raft's API does not yet say so
  (H5 (b), the raft fact, is R2s's).

**A Go finding** (nothing for `issues/`): replaying an older `ClusterVersionSet` after an upgrade
inside the window logs a spurious "downgrade detected", forces a disk snapshot and briefly lowers
the in-memory cluster version (`nonissues/etcd-cluster-version-restart-replay-downgrade.md`); the
rest model has no in-memory version, so the proof is unaffected.

#### Probe (2026-11-06, branch `r2dp`; DRAFT, nothing frozen)

The probe of (c) above (`/shared/tmp/r2d-prime-scope.md`, (c)), steps 1-2 of 5 done sorry-free, no new
axiom; steps 3-5 not reached in the session (no gap found; what is left is listed below).

- **Step 1, `restReplay_close`** (`RestReplay.lean`, proved): replaying any suffix of the committed log
  v2-only on its rest model gives it back. Over the server's facts (`ApplyRDefs.lean`'s
  `restReplay_closeI`: `srvRaftLogInv`, `srvRLogLb A₀`, `srv_committed_ccBoot`) it needs two premises
  the plan did not list: `c0 ≤ ai0` (so `c0 = 0`; `run`'s `hc0`) and **every entry of `A₀` normal or a
  v1 conf change** (`srvLogCore` gives `ccPolOk` for type-1 entries only; an entry of another type
  whose bytes decode as a v1 change is not excluded). Both are restart-point facts (`kvBatchR`).
- **Step 2, `apply` and `applyEntries` over `(rp, G)`** (`ApplyR.lean`'s `apply.wp_proofROff`,
  `ApplyEntriesR.lean`'s `applyEntries.wp_proofBatchROff`, proved, auth off), over two hypothesized
  replay specs (`ApplyRDefs.lean`): `applyEntryNormal.specRepOff` (the image `r` to `restEntryV2 m r`, the
  KV kept, the voters in `r.mem`) and `applyConfChange.specRep` (a replayed `AddNode`: no backend, no
  raft, no view, `ep.confState` kept, the peers kept). The loop invariant gains one variable, the ghost
  log `Γ = ghostOf rp (G ++ ms.take j)`; only `apply`'s `v3 = false` branch splits (replay or past the
  window); past the window `subst Γ` turns every row into lean's text and `wp_proofOff`'s code runs
  unchanged. The window closes inside the replay branch (`restReplay_closeI`, one `imod`). 1168 lines
  (about 180 new), 31 s to build.
- **What it shows for the design.**
  - The replay specs are smaller than A3/A4 assumed: `applyConfChange`'s replay needs none of the `v3`
    rows (`E.RO`, validation, `dvCCPre`), so A4 is a `v3 = false` case with no `dv` resources at all.
  - Under `kvBatchR` (`c0 ≤ ai0`, the batch's `v3` the model's past the window) **every entry past the
    window is `v3`**, so `applyEntryNormal.spec`'s ghost-advancing `v3 = false` case (an entry at or
    below `c0`) is dead in the window form: A3 can replace it by the replay case if `apply.spec` takes
    `c0 ≤ ai0` (which `run` has), keeping one spec split on `v3`.
  - `dvOk` at the ghost index (`g + 1`, Q19) refutes a past-window `v3 = false` conf entry as lean's
    does at `f0`; `dvRes` stays over Go's log, `dvView` over the ghost. A replayed conf entry needs a
    view (`dvOk`'s first clause), which the one-mode repair gives.
  - F2 needs no premise beyond `ai0 + |A₀| ≤ ciEff` (in `kvBatchR`); no `winNoConf`.
- **Not reached.** Step 3 (`applyResR`, `applyAll.specBatchR` hypothesized, `run_job_bodyR` for the
  straddling batch and the next, the law `applyResR` = `applyResC` past the window), step 4
  (`applyResR_start` over a drafted `Hsnap` restart form), step 5 (the view's round trip over a
  ghost-indexed `rnCfgAt`, finding 1); and the auth-on copy of `apply`'s proof (the same edit).
  **Est.: 4-6 d (est.)** for steps 3-5.
- **Steps 3-5 (done the same day, the second session; sorry-free, no new axiom, `applyAll.specBatchR`
  the only hypothesis).** This supersedes "Not reached" above, except for the auth-on copy of
  `apply`'s proof, which is still not done.
  - **Step 3** (`RunR.lean`). `applyResR K C rp A` is `applyResC` with these changes: the ghost rows
    at `ghostOf rp A` (`g`, `kvRunM`, `epCsAt`, `srvApRes`); `srvRestR`; `srvRLogLb A₀`; and the
    pure rows `uint.Z g = ai₀ + |ghostOf rp A|`, `ciJ`/`≤` at `g`, `rp.b ≤ |A|`, `A₀`'s types,
    `ai₀ + |A₀| ≤ ciEff` and `ai₀ + |A₀| + 1 < 2^64`. `applyAll.specBatchR` is the hypothesis:
    `specBatch` over the ghost, plus `winNoMergedSendR` (a DRAFT copy of `r2d-prime`'s
    `winNoMergedSend`, which is not on `lean`). `run_job_bodyR` is proved for any batch: inside,
    straddling or past the window. `applyResR_past` turns `applyResR` back into `applyResC` once
    `|A₀| ≤ |A|`, and `applyResR_first` turns `applyResC` into `applyResR` at `⟨0, []⟩`.
    Findings:
    - (a) The row `ai₀ + |A₀| + 1 < 2^64` is new. `dvOk` at `g + 1` needs it inside the window,
      where `srvIdxOk` bounds only Go's log. It is a restart-point fact: raft's next index after
      `A₀` fits.
    - (b) `applyAll`'s post keeps Go's `max ciEff ai'` form. `ciJ` steps at the ghost because
      `ai₀ + |A₀| ≤ ciEff` gives `max ciEff ai' = max ciEff g'`.
    - (c) `run_job_bodyR` keeps `run_job_body`'s `ai₀ = 0` and `γr.raft.pre = []`. Go's log `A`
      includes the handed prefix `P`, so the ghost log counts from index 1.
    - (d) A `match dv` written in a new declaration gets its own matcher, which `iframe` does not
      unify with the spec's. It is converted with `iExactEq H; cases dv <;> rfl`.
  - **Step 4** (`StartR.lean`). `rnSnapOnceR` is `Hsnap`'s restart form. It is `rnSnapOnce` at a
    given index and term, and its continuation gets `epCsAt γ A₀ cs` and `|==> memSnapLb γs 0` in
    place of `memSnapNone`. `rnSnapOnceR_first` shows today's `Hsnap` gives it at `A₀ = []`.
    `srvRestartAtR` is `applyStartC`'s restart form: the ghost index `g₀ = ciEff = ai₀ + |A₀|`, the
    rest buckets `srvRest A₀`, and Go's rows at `ai`. `srvRestartAtR_first` derives it from
    `applyStartC` given `c₀ = ai₀`. `applyResR_start` is proved: from these and `ep`'s fields it
    gives `applyResR` at `P`, with `rp = ⟨|P|, A₀⟩` and `P <+: A₀`. Findings:
    - (e) The start needs only `memSnapLb γs 0` of the storage. The restarted storage's token
      (B1's `memStorRestarted`) is a matter for the snapshot jobs, not for the start.
    - (f) `srvRestR` at `P` is `srvRest A₀` (`srvRestR_start`). `restReplay` replays nothing at
      `G = P`.
    - (g) The conf state's voters at `A₀` are the one new thing `Hsnap` must give.
  - **Step 5** (`ViewR.lean`). `rnCfgAtR γ rp L := srvCfgView γ.srv γ.nl [] (ghostOf rp (γ.pre ++
    L))`, which is `rnCfgAt` at a first start for any `pre`. `rnApGiveR`/`rnApRR` are the
    restart forms of `rnApGive`/`rnApR`. The bridges `rnApGiveR_dv`/`rnApRR_dv` replace
    `γ.pre = γs.pre` with the apply side's `pre = []`. `rnCfgR_replay` is the round trip: a batch
    inside the window leaves the ghost log unchanged (`ghostOf_replay`), so the view the apply
    thread got is the view it hands back. `rnCfgAtR_back_true` follows. Finding (h): A6's hub edit
    still needs the raft loop's names to carry `rp`. It also needs `rnCfgAt_normal`'s restart form
    (normal batches across the window), which needs the handed log to agree with `A₀` on the
    overlap, as `srvRLogLb` gives.
  - Builds: `RunR` about 7 s, `StartR` and `ViewR` about 2 s each. No gap was found and nothing
    was frozen.
  - **Revised R2d'a (est.):**
    - A6: 2-4 d. Its laws are drafted; the hub edit and the normal-batch law remain.
    - A9: 2-3 d. `Hsnap`'s form is drafted.
    - A10: 1.5-2.5 wk. The job body and the start's glue are done; still to do are the run loop's
      wiring, the snapshot jobs in a window, and the stop.
    - R2d'a in all: **4.5-6.5 weeks (est.)**.

#### R2d'a Draft (2026-11-06, branch `r2dp`; DRAFT, nothing frozen)

Tasks A3, A4, A5, then the auth-on copies. A4 is proved. A3 and A5 stopped under H9, each with a
proposal below. The auth-on copies were not started, because their replay hypothesis is A3's
statement. Lean was frozen, so nothing landed.

- **A4, proved** (`ApplyConfChangeR.lean`, `EtcdServer.applyConfChange.wp_proofRep`, from the body
  over the callee specs of lean's `applyConfChange.wp_proof`). Go at `673da07c8`: the validation
  returns `nil` without reading (`membership/cluster.go:306-309`), raft is not called
  (`server.go:2053-2059`), `SetConfState(ep.confState)`, the context unmarshalled, `AddMember(…,
  false)` (`cluster.go:395-424`) and `AddPeer` of a known peer. **DRAFT statement change**
  (`specRep`, a premise the caller already had): `E.RO rs` in and out, with the frozen spec's
  `HRO` shape, and the members' size bound. `ValidateConfigurationChange.spec` and
  `AddMember.spec` take the cluster's `be` field even at `v3 = false`, and `AddMember` takes its
  in-memory members (`clusterMem`) and their bound. Only `E.RO` holds them. The caller
  (`ApplyR.lean`'s replay branch) supplies them through `srvRestRp_ro`, and the bound through
  `srvApRes_ccRep`, whose pure conjunct now also gives the bound for any image with the keys of
  `restModel A₀` (`restReplay_memKeys`). `ApplyR`, `ApplyEntriesR`, `RunR`, `StartR`, `ViewR`
  rebuilt. `#print axioms`: no `sorryAx`; the axioms are a subset of lean's
  `applyConfChange.wp_proof`'s (`apply.wp_proofROff` adds three that are already in
  `etc/tcb-baseline.txt`).
- **A3, STOPPED (H9): `applyEntryNormal.specRepOff` cannot be proved from the frozen leaf
  specs.** `apply.Apply.specRec` (`apply/ApplyRec.lean:67`), `uberApplier.Apply.spec` and
  `uberApplier.dispatch.spec` require these premises at every `v3`: `grantFresh E rq U` (the
  request's grant id not in the lessor's ever-ids `U`, unless the lessor is monotone),
  `cmpAdmit`, `cmpPermRq` and `grantPermRq`. Go at `v3 = false` reads none of them:
  `dispatch` returns `nil` after its first `switch` (`apply/uber_applier.go:117-119`), and the
  proof of `dispatch` uses them only in its `v3` branch (`uberApplier__dispatch.lean:389`, then
  :549, :608-613). For a replayed revocable-mode `LeaseGrant`, `grantFresh` is **false**:
  `everOwn E U` is the exact half of the lessor's ever-set (`lease.leaseEver`, a ghost variable),
  and the replayed grant's lease, when it is still live, is in that set. No premise the caller has
  can give it. `cmpAdmit` and `cmpPermRq` of a replayed compaction would also need the KV model
  (`kvApplied` at the ghost log, `kv_entry_claim` for an entry inside the log), which
  `specRepOff`'s pre does not take. The other premises have sources: `rqOk`/`dispatchOk` from
  `entryOk`, `restReqOk` from the members premise (`restLeasesWith_mem`), `ltHalf`/`everOwn` from
  `srvRestRp`'s `srvRestAt`/`srvEver`, `revokeOwn` from `srvApplyKV`.
  - Options. **(a)** Guard the four premises by `v3` (`if v3 then … else True`) in
    `dispatch.spec`, `uberApplier.Apply.spec` and `Apply.specRec`. These are frozen, internal
    statements, and the change only weakens their preconditions. The proof edits are small:
    `dispatch` already splits on `v3` first, the other two pass the premises through, and the
    callers (`applyEntryNormal`'s off/on proofs, which reach these specs through `spec_rec`)
    weaken with one lemma per premise. Est. 1-1.5 d plus the Freeze review. **(b)** New
    `v3 = false` triples (`dispatch.specV2`, `uberApplier.Apply.specV2`, `Apply.specRecV2`) proved
    beside the frozen ones, with no frozen statement changed. This duplicates `dispatch`'s first
    `switch` (about 200 lines) and two pass-through proofs. Est. 2-2.5 d. **(c)** Exclude
    replayed revocable grants from `specRepOff`. This is false of Go runs; rejected.
  - **Recommendation: (a).** It states what Go does: a `v2`-only apply reads no grant,
    compaction or permission state. It fits H2's one `applyEntryNormal.spec` with a `v3` case,
    and it costs least. It needs 82's go, since it edits frozen statements.
- **A5, STOPPED (the brief's rule: the merged-send branch needs more than `winNoMergedSendR`).**
  The branch's message comes from `msgSnapC`'s bag (`isRNMsgSnapC γm`, `rnSnapMsg`). It is a
  `MsgSnap` that `γm.id` sent (`sentMsg … γm.id st`). `winNoMergedSendR` speaks of the
  messages of `id` with `srvMemberIDAddr s ↦□ id`. On `lean`, `isServerApplyAll`
  (`InvApplyAll.lean:119-147`) relates `γm` to the server only by `γm.node = γr.raft.raft`, and
  nothing in `specBatchR`'s pre ties `γm.id` to the member id (the transport's `lid` is not tied
  either). So the merged-send branch inside a window cannot use the premise. This is A7's
  "member-id conjunct" (frozen at `r2d-freeze1`, not on `lean`). Options:
  - **(a)** Bring A7's `isServerApplyAll`/`srvApplyAllBuilt` conjunct `γm.id = memberID` into
    this branch: a hub edit, which `NewServer` already knows (est. 0.5-1 d with its supply).
  - **(b)** State `winNoMergedSendR` over the bag's names (`∀ γm, γm.node = γ → isRNMsgSnapC γm
    msc → …γm.id…`). This moves the same fact to A7's supplier at `run`, which needs the same
    link. Not simpler.
  - **(c)** Quantify over every sender. This would say no member sends a `MsgSnap` at `rt` while
    the window is pending, which is false (the leader does). Rejected.
  - **Recommendation: (a).** Two more facts, needed outside the window as well: lean's proof of
    the merged branch (`EtcdServer__applyAll.lean:375-450`) uses the KV at Go's index (`hciE`,
    `merged_imageC` at `A ++ batch`). It therefore applies unchanged only once the window closes
    after the batch. That is exactly when `winNoMergedSendR` is `R = []`, and there
    `ghostOf_past` and `srvRestR_past` turn every row into lean's. `snapshotIfNeeded…`'s spec
    (`hSINC`) takes Go's rows only (`srvSnapStor` at `A ++ batch`, `ai' ≤ ciEff`, which holds
    inside the window since `ai' ≤ g' ≤ ciEff`). Separately, `applyAll`'s R proof also needs a
    mode-generic `applyEntries.specBatchR`, the window form of `specBatch` (`ApplyEntriesR.lean`
    has only the off form). Its proof from the off and on forms is `wp_proofBatch`'s case split
    (about 60 lines).
- **The auth-on copies (`apply.specROn`, `applyEntries.specBatchROn`): not started.** They take a
  hypothesized auth-on replay spec, `applyEntryNormal.specRepOn`. With A3's recommended shape,
  that becomes one mode-generic statement (H2), so drafting an on-only copy now would be redone.
  The copy itself is mechanical: lean's `apply.wp_proofOn` (`EtcdServer__apply.lean:1005`, 830
  lines) with the probe's ~180-line window edit. Est. 2-3 d.
- **The row `ai₀ + |A₀| + 1 < 2^64` (`applyResR`; the coordinator's question): no existing
  statement supplies it at a restart.**
  - `bootstrapRestartContract` (`InvRestart.lean:563-583`) gives the image's consistent index `i`
    as a `w64` with `uint.nat i ≤ σ.commit` (:567-570). So `ai₀ + |A₀| = i < 2^64`, but not `+ 1`.
    `imageAt` (`InvImage.lean:114-119`) adds nothing about indices.
  - `srvIdxOk` (`KVModelDefs.lean:249-250`, `ai₀ + 1 + |L| < 2^64`) holds only of logs raft hands
    (`rnEnvOk`'s `E.C`, `InvRaftNode.lean:483-486`). `A₀` is handed only when Go's log reaches
    `i`, which closes the window. Inside the window it bounds only Go's shorter log.
  - `srvRLogLb` (`SrvRaftLog.lean:395-396`) carries only `srvIdxOkW` (consecutive indices).
  - The cindex specs bound nothing. `NewServer`'s restart branch is R2d'b (B5) and does not
    exist yet.
  - The candidates: a premise of `bootstrapRestartContract` (`uint.Z i + 1 < 2^64`, a fact about
    the data directory, like `N + 7 + bootWB ≤ wbInit`), or the raft loop's restart data (raft
    must already prove `E.C`'s introduction law, `ai₀ + 1 + |L| < 2^64`, for the log through
    `σ.commit ≥ i` that it will hand). The second is cheaper to justify, since it is raft's own
    obligation.
- **Revised R2d'a (est.):** A3 with (a) 1-1.5 d; the on copies 2-3 d; A5 0.5-1 d for the A7
  conjunct plus 3-4 d for the proof (lean's 420 lines and the merged `applyEntries.specBatchR`);
  the rest as in "Revised R2d'a" above. **R2d'a in all: 4.5-6.5 weeks (est.), unchanged.** The
  stops add no new work item; they move A7's conjunct earlier.

##### R2d'a Draft, pass 2 (2026-11-06, after 82's decisions: A7's conjunct now, A3 with the user)

- **A7's conjunct, in (DRAFT hub edit, 82's go).** `isServerApplyAll` (`InvApplyAll.lean`) and
  `srvApplyAllBuilt` (`InvStart.lean`): `(∃ γm : RNNames, ⌜γm.node = γr.raft.raft⌝ ∗
  isRNMsgSnapC γm msc) ∗` → `(∃ γm : RNNames, ⌜γm.node = γr.raft.raft⌝ ∗ srvMemberIDAddr s ↦□
  γm.id ∗ isRNMsgSnapC γm msc) ∗` (`r2d-window-full`'s text). `NewServer` produces it from its
  `memberID` field (`γrn.id = id`). `start` copies the conjunct whole. `ApplyAllSnap`,
  `ApplyAllSnapOn` and `EtcdServer__applyAll` destructure one more item. No first-start statement,
  closed theorem or caller premise changed. The 23 modules that mention the two predicates were
  rebuilt; the full build is the check of the closed theorems.
- **A5, proved** (`ApplyAllR.lean`). `applyEntries.specBatchRAt P` is the mode-generic window form
  of `specBatch`. `specBatchR` is the form at `· ≠ .any`, and `applyEntries.wp_proofBatchR` proves
  it from `specBatchROff` (proved, `ApplyEntriesR.lean`) and **`specBatchROn` (HYPOTHESIZED; it
  waits for A3's on copy)**. `applyAll.wp_proofBatchR : applyAll.specBatchR` takes lean's
  hypotheses, but `applyEntries.specBatchR` in place of `specBatch`. The proof is lean's
  `wp_proofBatch` with these changes: the ghost index `g'` comes from the batch's post;
  `Trigger(ai')` gets `appliedAtLeast ai'` from `g' ≥ ai'` (`monoNatLbOwn_le`); and the merged
  send uses `winNoMergedSendR` with the new conjunct. Either the window has closed after the
  batch, or the message (this member's `MsgSnap`) is not at the batch's term `rt`. In the branch
  where `Term = rt`, the window is closed: `ghostOf_past`/`srvRestR_past` turn every row into
  lean's, and `g' = ai'`. No other DRAFT statement change.
- **A6's normal-batch law, restart form** (`ViewR.lean`). `rnCfgAtR_normal`: a batch of normal
  entries keeps `rnCfgAtR γ rp L` → `rnCfgAtR γ rp (L ++ ce)`, given that Go's log through the
  batch and `A₀` are prefix-comparable (`ghostOf_batch`: the ghost log grows by a suffix of the
  batch). `rnCfgAtR_back_false` is `rnCfgAt_back_false`'s analog (`ccIn ce = false`).
- `#print axioms` (`applyAll.wp_proofBatchR`, `applyEntries.wp_proofBatchR`, `rnCfgAtR_normal`,
  `rnCfgAtR_back_false`, `ghostOf_batch`): no `sorryAx`, and no axiom outside lean's
  `applyAll.wp_proofBatch`'s.
- Left: A3 (with the user), then `specBatchROn`'s and `apply.specROn`'s proofs (2-3 d after A3).

##### A9: stopped before the hub edit (Q20; 2026-11-06)

`run.wp_proof` (`EtcdServer__run.lean`) reads `%HEr`'s first-start conjuncts, `γn.pre = []` and
`ai₀ = 0`, in every job arm. The snapshot arm (:1129-1130), the normal arm (:1206-1212, `hdvs`'s
`ρ.raft.pre = []`) and the batch arm (:1242-1243, `rnAdvChan`'s `uint.nat ai₀ + |A ++ ce| = |γn.pre
++ A ++ ce|`) all use them. So do `run`'s helpers (:86, :301, :508, :685: `hpre : γn.pre = []`,
`ha00`) and `RunOn.lean:99-100`. With `%HEr` at `P <+: A₀` and `Hstart = srvRestartAtR`, the proof
would have to handle every `A₀`, which is A10. So the hub edit cannot land without A10's proof
unless `run` reaches a DRAFT `sorry`, which Q20 forbids. Not edited. The plan: A9's texts
(`InvRun.lean:53-54`, `InvStart.lean:240-241`, `RunOn.lean:99-100`, `Hsnap`, `Hstart`) are written
together with A10's restart branch of `run.wp_proof`, and both land as one change. The
first-start supply goes through `rnSnapOnceR_first`/`srvRestartAtR_first` (`StartR.lean`) at
`⟨0, []⟩`. The bound `ai₀ + |A₀| + 1 < 2^64` becomes a conjunct of the raft side's restart data in
the same edit. Then A3 was unblocked (Q22 (1) (a), user-approved) and took priority.

##### A3 (Q22 (1) (a), user-approved; 2026-11-06)

- **Step 1: the frozen specs weakened** (DRAFT, for the Freeze package). In `dispatch.spec`
  (`Spec/…/apply/uberApplier__dispatch.lean`) and `uberApplier.Apply.spec`
  (`Spec/…/apply/uberApplier__Apply.lean`), with `L` = `log` and `x.log` respectively:
  - old: `⌜apply.rqOk E.lm L rq ∧ apply.dispatchOk E.authOn rq ∧ apply.cmpAdmit E.γ.kb L rq⌝ ∗
    apply.cmpPermRq E rq ∗ apply.grantPermRq E rq ∗ apply.ltHalf E T ∗ apply.everOwn E U ∗
    apply.grantFresh E rq U ∗`
  - new: `⌜apply.rqOk E.lm L rq ∧ apply.dispatchOk E.authOn rq ∧ (v3 = true → apply.cmpAdmit
    E.γ.kb L rq)⌝ ∗ □ (⌜v3 = true⌝ → apply.cmpPermRq E rq) ∗ □ (⌜v3 = true⌝ →
    apply.grantPermRq E rq) ∗ apply.ltHalf E T ∗ apply.everOwn E U ∗ □ (⌜v3 = true⌝ →
    apply.grantFresh E rq U) ∗`

  In `Apply.specRec` (`Proof/…/apply/ApplyRec.lean`):
  - old: `… apply.dispatchOk E.authOn rq ∧ apply.cmpAdmit E.γ.kb x.log rq ∧ apply.restReqOk rq rs⌝ ∗
    apply.cmpPermRq E rq ∗ apply.grantPermRq E rq ∗ apply.ltHalf E T ∗ apply.everOwn E U ∗
    apply.grantFresh E rq U ∗`
  - new: `… apply.dispatchOk E.authOn rq ∧ (v3 = true → apply.cmpAdmit E.γ.kb x.log rq) ∧
    apply.restReqOk rq rs⌝ ∗ □ (⌜v3 = true⌝ → apply.cmpPermRq E rq) ∗ □ (⌜v3 = true⌝ →
    apply.grantPermRq E rq) ∗ apply.ltHalf E T ∗ apply.everOwn E U ∗ □ (⌜v3 = true⌝ →
    apply.grantFresh E rq U) ∗`

  The edit only weakens preconditions. Why the `□ (⌜v3 = true⌝ → …)` form: the three are
  persistent, and the form keeps the callers' `#` patterns. `dispatch`'s proof takes them at
  `v3 = true` (four lines in its `v3` branch); `Apply`'s and `spec_rec`'s pass them on unchanged.
  `applyEntryNormal`'s four call sites gate what they had (`apply.v3Gate`, `ApplyRec.lean`). None of
  the three is in a package with a committed interface (`etc/api/` has `raft`, `backend` and
  `etcdstart` only), so `gen-interface --check` does not apply.
- **Step 2: the replay proved.** In `ApplyEntryNormalR.lean`, `applyEntryNormal.wp_proofRepOff :
  specRepOff` and `wp_proofRepOn : specRepOn`.
  - **DRAFT fix to `specRepOff`**: `srvRLogLb γr.raft A₀ ∗ ⌜m ∈ A₀⌝`, which the caller has
    (`kvBatchR`'s `HlbA0`, and `hpA` gives `m ∈ A₀`). The KV invariant's shape of a committed entry
    (`kv_log_plain`) is what makes a skipped or rejected request leave the members, as
    `restEntryV2` says.
  - **`specRepOn` is new.** It has `specRepOff`'s rows in mode `on`: `isServerM true`,
    `srvApplyKVOn` at a kept auth state, `⧗ 1`, the receipts' bound, and `x.chain = γr.kv.ch0`. An
    admin request runs `adminEntryOn` at `v3 = false`, which needs the chain. The caller's
    `kvAppliedM` gives it.
  - **Two mode-specific specs, not one mode-generic `specRep`**: the replay's resources differ by
    mode (the auth row and its state, the credit, the chain), and so do its callers, the off and
    on loops (`apply.specROff`, the future `apply.specROn`), as lean's `applyEntryNormal.specOff`
    and `specOn` do. A generic statement would only be unfolded again at each caller. Merging the
    replay into the frozen `applyEntryNormal.spec` as its `v3 = false` case would not fit either:
    that spec's `v3 = false` case is the first start's (ghost rows stepped, `srvRest` at `A ++ [m]`).
- **Step 3, the on copies (`apply.specROn`, `applyEntries.specBatchROn`): not done.**
  - The plan for `apply.specROn`: `git merge-file` of lean's `apply.wp_proofOff` → `wp_proofOn` diff
    onto `ApplyR`'s `wp_proofROff` leaves 14 conflict hunks, all in the invariant's rows and the
    `iexists` lists, each a mechanical union of the two sides.
  - What a merge does not give:
    - the replay branch in mode `on`: `hAENR` → `specRepOn`, which needs a `⧗ 1` (a second
      `wp_go_step_receipt'` before the call, as the normal branch's) and the chain fact from `Hka`;
    - `ApplyR`'s copies of the conf-change macros in their `On` forms (`cc_kv_appliedOn`,
      `cc_respondOn`, local to `EtcdServer__apply.lean`).
  - `applyEntries.specBatchROn` is then `ApplyEntriesR`'s 220 lines merged the same way. Est. 2-3 d
    (unchanged). Until then `applyEntries.wp_proofBatchR` takes `specBatchROn` as its one hypothesis.
- `#print axioms` (`applyAll.wp_proofBatchR`, `applyEntries.wp_proofBatchR(Off)`,
  `apply.wp_proofROff`, `applyEntryNormal.wp_proofRep{Off,On}`, `applyConfChange.wp_proofRep`,
  `rnCfgAtR_normal`, `rnCfgAtR_back_false`): no `sorryAx`, and nothing outside lean's
  `applyAll.wp_proofBatch`'s, except `apply.wp_proofROff`'s three (`apply.memberKey_inj`,
  `membership.membersOfBk_empty`, `membership.membersOf_decode`), which are in
  `etc/tcb-baseline.txt`.
