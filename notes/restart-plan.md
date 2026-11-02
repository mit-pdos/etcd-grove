# Plan: restarting a member (`examples/restart3`)

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

`examples/restart3` is putget3 with a restart:

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

What stays out: crashes (Q4), membership changes (the membership track), restarting the leader
mid-request (Q6), and a member whose data directory was lost.

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

## Size and order

- **Largest:** L1 (M6: every request path gains a token) and L4 (raft's restart, the durability
  work's).
- **Moderate:** L5 (mostly the snapshot install's restore, reused) and L3 (a contract, unless Q3
  (b)).
- **Small:** L0, L2 and L7.

R1 can start now. R2 can start once Q1-Q6 are answered, with L4 as a named `sorry` if Q2 says the
durability work comes first.

## R1 (2026-11-02)

- `examples/restart3` (`restart3.go`): `Run(lg)` is the program at a logger, `Main` is `Run` at
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
  prefix, from the wall clock (`issues/etcd-request-id-restart-reuse.md`). The cluster's map of
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
(`issues/etcd-request-id-restart-reuse.md`), and what the image holds of raft (R2e) and of the
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
the issue's precondition (`issues/etcd-request-id-restart-reuse.md`): the clock does not step back
and a member issues fewer than 256 ids per millisecond on average. It is an assumption about the
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
