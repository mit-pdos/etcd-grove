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
