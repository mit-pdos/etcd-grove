# Plan: restarting a member (`examples/restart3`)

**Date:** 2026-11-02. **Status:** Scope, drafted; the questions Q1-Q6 below are open (the user's).
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

## Questions for the user

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
