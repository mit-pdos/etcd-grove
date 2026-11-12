# Batch 2d, provability review, round 1

Reviewer: provability (independent of the author). Worktree `specs-only` at `011846a908`.
Targets: `SpecPlan/Spec/go_etcd_io/etcd/server/v3/etcdserver/ApiApply.lean` and the 2d specs beside it,
`.../etcdserver/cindex/`, `SpecPlan/Spec/go_etcd_io/etcd/pkg/v3/schedule/`, snippets
`examples/specreq/{etcdserverapply,cindex,schedule}/`, the `## from 2d` requests. Go: server
`a4d2bb17` (`$S` = `.../server/v3@v3.0.0-20261107170612-a4d2bb1720b9`), raft `565c2bd`.
`go vet` of the three snippet packages passes. I wrote my findings before reading
`batch-2d.md`. Its open question 2 (the proposer-dependent model) is F1 below. F1 shows the
looseness it describes is not stated anywhere a proof could use it.

## What is good

- **The overall scheme is right, and much simpler than the old one.** Updates fire at commit,
  inside raft's proposal update (`histPropose`), not at apply. So "fired exactly once" is raft's
  `dup = false`, and no apply fires anything. The history is the committed log's, so a restart, a
  snapshot install or a replay is a member's position in one history, not a window. It answers
  the brief's question (a): the proposer's update fires once, at the commit, by raft. No member
  fires it at its apply.
- **Restart (b) needs nothing beyond RestartNode, apart from 2e's durable facts.** The spec has
  none of the R2d'a premises.
  - `Applied = 0`, so the delivered log starts at the storage offset `si`, and `p₀.appliedi = si`.
  - The node's view is at the backend's point (`nodeConf ⟨ci₀, m⟩`, with `a ≥ σ.off` allowed by
    `RestartNode.spec:76`).
  - The replay below `ci₀` never calls raft. For `v3 = false`, `ValidateConfigurationChange`
    returns `nil` (`$S/etcdserver/api/membership/cluster.go:307`), and the membership writes are
    no-ops (`cluster.go:402-424`).
  - I checked that `ci ≥ appliedi` holds at every point:
    - every `v3` apply moves `ci` to `k` (`server.go:1971-1979`, `2040-2044`, and the hook at
      `2478`);
    - a restart has `ci₀ ≥ si` (bootstrap recovers from `.snap.db` otherwise);
    - an installed image has `k ≥ sn.index`.
  - So "the state machine at `max appliedi ci`" is always at `ci`.
  - `verifyConsistentIndexIsLatest` and `ReqReplayBelowCI` are sound.
  - The worry that the backend persists `meta/confState` ahead of `ci` is real but harmless. A
    periodic commit between `SetConfState` (`server.go:2055`) and `AddMember`'s `LockInsideApply`
    saves `(k-1, conf_k)`. But nothing reads `meta/confState`: the restart rebuilds the
    configuration from the members bucket (`bootstrap.go:112`, `buildConfStateFromV3store`).
- **The durability argument holds.** A follower's acknowledgements leave only after `Save` fires
  `readyEnter`. The leader sends before its write by `readyCheck`. A commit-only `Ready` that is
  not synced is covered by R1's `wcommit`. The `applyc` send before `Save` is fine: the entries
  are committed by `readyGot`.
- The merged-snapshot guard is the fork's code, with no window premise.
- `applyEntries` and `applySnapshot` derive their panic-freedom from `BatchOk`:
  - `firsti = B.base + 1`;
  - `B.prev < sn.index`.
- **`schedule`** is sound against `schedule.go`. All three snippets are provable:
  - `Stop` waits for `donec`, and the worker runs every pending job, including the jobs taken in
    its `ctx.Done()` branch, before it closes `donec`.
  - `schedOpen` excludes the `Schedule`-after-`Stop` panic.
  - `Pay` is the right way to state `compactBarrier`'s early return.
  - `ReqCancelledCtx` is proved with a monotone flag as `Pay`.
- **`cindex`** is a clean TaDa vocabulary. All three snippets are provable from the specs:
  - `UnsafeSave`'s `c ≤ m.idx` premise is exactly the `verify` check (`schema/cindex.go:77-84`).
  - The skip of index `0` is in the post.

## First tier

**F1 (a, d). `histPropose` together with `applyThread` "at `histAt`" cannot be realized as
stated; the member-configuration scheme is missing.**
- *Evidence.* `histPropose.spec` (`ApiApply.lean`) quantifies over any `mc : MemberCfg`. The
  history's next point is `σ'` with `applyStep mc σ e σ' res`.
- Every member's `applyThread` claims its state machine is at `histAt γ k σ'`. Each member
  actually applies at its own configuration: the lessor clamps the TTL to its own minimum
  (`nonissues/etcd-lease-ttl-differs-across-members.md`; W0's `LeaseRec.ttl` records it,
  `Model.lean:958-960`).
- No law says `σ'` is independent of `mc`, not even up to a member-state relation.
- Nothing ties the `mc` the proposer passes to its own member. So nothing makes "the proposer's
  apply computes the answer fixed at commit" provable. That claim is `answered`, 2c's
  `applyResult`, and `req/...etcdserver_apply.md` "from 2d" item 2.
- The author's "relate loosely" (`batch-2d.md`, Q2) is not stated in any law or realization that
  3a or 2c could rely on.
- *Affects.* 2c's `processInternalRaftRequestOnce.spec`, which must pick `mc`; every member's
  `applyEntryNormal.spec`; `applySnapshot.spec`, since `lessor.Recover` re-clamps.
- *Fix.* Either:
  - (i) make the history configuration-free. W0's `LeaseRec` records the asked TTL, or none;
    `res` alone carries the granted TTL. Add a law `applyStep_cfg : applyStep mc σ e σ1 r1 →
    applyStep mc' σ e σ2 r2 → σ1 = σ2`, and a persistent `srvCfg s γ mc` (from `srvNode`) that the
    proposer uses, so the answer is its own. Or:
  - (ii) take the premise "all members configured alike" at `NewServer`, and fix `mc` in `Names`
    (`γ.mc`) instead of quantifying.
- Either way, also state the law `applyStep_reach : applyStep … σ σ' … → Reach σ σ'`. The
  realization of W0's `etcdLb_reach`/`etcdLb_ord` needs it, and today it is only prose in the
  request to 3a.

**F2 (`run`). `applyc_recv` loses the batches' order, so `run` cannot meet `applyAll`'s premise
`⌜p.appliedi = B.prev⌝`.**
- *Evidence.* `applyc_recv.spec` gives `∃ B, applyBatch r γ apv B false`, with nothing relating
  `B.prev` to the previous batch's `B.last`.
- `run.spec`'s sketch keeps the chain at `p.appliedi = delivered` (step 5), but no law gives the
  receiver "delivered".
- The job runs `applyAll(&ep, &ap)` (`server.go:840-842`), whose spec requires
  `uint.nat p.appliedi = B.prev`.
- *Affects.* `EtcdServer.run.spec`, `ReqWriteAnswered`, `ReqAppliedRead`.
- *Fix.* Add an exclusive cursor `applycPos r k`. `applyc_recv` takes it and returns it with
  `B.prev = k` and `applycPos r B.last`. `srvRunTok` carries `applycPos r p₀.appliedi`.

**F3 (c). Who owns R1's `nodeConf`: the realization gives it to the apply thread, but the loop
needs it at every `Advance`.**
- *Evidence, the ownership.* The header's realization of `applyThread` contains "R1's
  `nodeConf`".
  - `node.Advance.spec` (`node__Advance.lean:52-55`) takes `nodeConf n γ v` at every `Advance`.
  - The loop advances a batch without conf changes, a snapshot batch included, without waiting
    for the apply thread: it waits only `if confChanged` (`raft.go:317, 337`). The apply thread
    may still be on earlier batches (the FIFO queue).
- *Evidence, the snapshot batch.*
  - `Advance` returns a wand that needs `confAt γ a m` with `s.conf.Is m`. The loop must apply
    it itself: it advances again (`raft.go:347-353`) before the apply thread can receive
    `raftAdvancedC`.
  - The loop can only take `a` from `snapValid_committed`.
  - The apply thread's state machine is at the image's consistent index `k`. No law says that
    `k` is that `a`: `snapImage_hist` gives only `histAt γ s.index`.
  - `applySnapshot.spec`'s sketch ("`confAt γ.raft a m` with `a = k` once the image's records
    are read") assumes the apply thread applies the wand, which the code's interleaving rules
    out.
- *Affects.* `raftNode.start.spec` (steps 7-8), `applySnapshot.spec`, `applyConfChange.spec`, and
  the realization of `applyThread`.
- *Fix.*
  - Make `nodeConf` the loop's. It is lent to the apply thread through `applyBatch` for a batch
    with conf changes and returned through `notifyc`'s blocking second send (`raft.go:317-324,
    337-343`).
  - Make the snapshot's configuration point recoverable by both threads. Add a law
    `snapImage_point : snapImage γ s ⊢ ∃ a m σ, histAt γ a σ ∗ confAt γ.raft a m ∗ ⌜s.index ≤ a ∧
    s.conf.Is m⌝`, with the image's stored index being that `a` (2e's `OpenSnapshotBackend`).
    Or have R1's `snapValid` name its point.
  - Restate `applyThread`'s realization as "the view at the thread's point, or at the loop".

**F4 (c). No stated source for `snapImage` of a batch's snapshot.**
- *Evidence.* `raftNode.start.spec` step 4 hands `applyBatch` "the snapshot's validity and
  `snapImage`". R1's `readyGot` gives only `snapValid`.
- `snapValid` also holds of the in-memory snapshots made by `snapshot()` (`snap_make`,
  `server.go:2133`). They have no `.snap.db`, so the cluster's invariant cannot give
  `snapImage` for every valid snapshot.
- The planned path (`req/...rafthttp.md` "from 2d" item 5: `dbSaved` kept "from `Process` to the
  install" for index `i`) is keyed by the index alone.
- *Uncertain.* Two merged snapshots of one index can carry different images and configurations:
  - a leader still replaying sends `ep.confState` of `ci > appliedi`;
  - a later leader at the same `appliedi` sends the configuration of `appliedi`.
  - The receiver's `<i>.snap.db` may then hold the image that does not match the `ConfState` its
    `Ready` installs. I did not find a wrong result (R1's idempotent re-apply may absorb it), but
    the invariant as described breaks.
- *Affects.* `applySnapshot.spec`, `raftNode.start.spec`.
- *Fix.* State in `ApiApply.lean` the member-local invariant from which `applyBatch` gets
  `snapImage`, keyed by the snapshot itself (index and configuration), not the index. Or show
  uniqueness per index.

**F5 (c). The merged snapshot's term premise has no source.**
- *Evidence.* `createMergedSnapshotMessage.spec` requires `p.appliedt ≤ m.term`. `applyAll`'s
  sketch derives it from `m.term = B.term` and "applied terms ≤ the hard state's term (R1)".
- That bound is not in R1 at `HEAD`:
  - `BatchOk` (`raft/v3/Model.lean:442-453`) and `readyGot` have no term fact;
  - the request (`req/go_etcd_io_raft_v3.md` "from 2d" item 1) is unserved;
  - `R1-round2.md:99` asks for it.
- The bound is also not enough alone. After a restart, `raftTerm` starts at `0`
  (`raft.go:183`). It changes only on a non-empty `HardState` (`raft.go:223`). So `B.term = 0`
  while `appliedt` is the storage snapshot's term. The guard `m.GetTerm() == apply.raftTerm` is
  safe only because a sent `MsgSnap` has term `≥ 1`, a fact R1 does not state.
- *Affects.* `applyAll.spec`, `createMergedSnapshotMessage.spec`, `ReqMergedSnapshot`.
- *Fix.* R1 adds:
  - to `BatchOk`, the term bound on the batch's committed entries and snapshot;
  - the start's snapshot term `≤` the driver's hard-state term;
  - `msgSent_type`-style `m.type = MsgSnap → m.term ≠ 0`.
- `applyBatch`/`applyThread` carry `B.term = 0 ∨ p.appliedt ≤ B.term`.

**F6. Snippet `ReqAppliedRead` is false of Go.**
- *Evidence.* `applySnapshot` never stores `s.appliedIndex`; the only stores are at
  `server.go:1944` and `1952`, per entry. `applyAll` triggers `applyWait` at `ep.appliedi`
  (`server.go:985`), which after an install is the snapshot's index.
- So a waiter at `i ≤ sn.index` wakes while `getAppliedIndex() < i`, and the snippet's panic
  fires.
- The specs agree with Go. `getAppliedIndex.spec` gives only `srvApplied s γ v` of the stale
  `v`, and `applyAll.spec` says nothing about the atomic.
- No real user relies on the atomic after the wait. `read.go:130-136` waits, then serves from
  the store.
- *Fix.* Panic on what the wait really gives (`srvApplied s γ i`, e.g. a store read at `≥ i`, or
  `ReqReadIndex`-style). Drop "its applied index is at least i" from the header.
- Possibly a `nonissues/` entry: the stale `appliedIndex` after an install makes
  `exceedsRequestLimit` (`v3_server.go:1060-1064`) and Maintenance's `RaftAppliedIndex` lag until
  the next entry. I have not written one: this review is read-only.

**F7. Snippets reach into the raft node with no law to do it.**
- *Evidence.* `ReqSnapshotCompact` (and `ReqDriverLoop`'s `FirstIndex`) call
  `s.r.raftStorage.Snapshot()` and `Term()` after `snapshot`/`compactRaftLog`. The post gives
  `nodeSnapLb r appliedi`, and the batch gives `nodeAdvanced`.
- No law turns these into R1's `storSnapLb`/`appliedLb` of the node.
- `isRaftNode` exposes no `s.r.raftStorage ↦□ ms ∗ nodeStorage n γ.raft (memStor ms)`.
- So the panics on `Snapshot().Index < appliedi` and `Term ≠ ok/ErrCompacted` are not provable
  from the API.
- *Fix.* Add the laws `isRaftNode_storage`, `nodeSnapLb_stor : isRaftNode r γ id n ∗ nodeSnapLb r
  k ⊢ storSnapLb n k`, and `nodeAdvanced_applied`.
- Also add `msgSnapC_recv` (`applyAll` and `ReqMergedSnapshot` receive on `s.r.msgSnapC`; there
  are laws for `applyc` and `readStateC` only), giving `msgPts`, `msgSent`, `m.type = MsgSnap`,
  `m.src = id`.

**F8. Snippet `ReqConfChangeAnswered` relies on more than the registry predicate 2d specified.**
- *Evidence.* Its last panic needs "`err = nil` → `membs` lists the node".
  `req/...etcdserver.md` "from 2d" item 3 gives 2c's `P` for a conf change only `advancedAt`.
- *Fix.* Add the clause, from `s.cluster.Members()` read after an accepted change (2e's
  membership), or drop the panic.

**F9. Snippets' `Assumes` miss what makes them true.**
- `ReqRestartContinues` and `ReqCrashKeepsAnswered` assume nothing about other writers. Another
  client's `Put`/`Delete` of `k`, or a delete through a lease, makes the panic reachable. Add "no
  other client writes `k`; no lease on it".
- `ReqLeaseExpiry` misses "`id` is not granted again". A re-grant of `id` and a `Put` with it
  between `TimeToLive` and `Get` shows a key with lease `id`.

## Second tier

- **S1. `histPropose` needs raft's namespace inside `etcdN`.** Raft fires the built update at
  `⊤ ∖ ↑γ.raft.ns`. The update opens the cluster's invariant and must fire the client's at
  `⊤ ∖ ↑etcdN`. That works only if `↑γ.raft.ns ⊆ ↑etcdN` and the invariant's own namespace is
  disjoint from it. Neither `Names` nor any law says so. Add it to `Names` (2e's allocation).
- **S2. `histPropose`'s `D` may admit `bs = []` with `ty = EntryNormal`.** `opsOf` drops it
  (`raft/v3/Model.lean:129-130`), so the update would step the history with no op. Add
  `ty = EntryNormal → bs ≠ []`.
- **S3. The realization of the history is mis-stated.**
  - It says `|hist| = |committed log|` and keys `answered` by log index.
  - But the invariant owns only `committedOps`. Raft fires nothing for fillers, and the proposal
    update reveals no index.
  - So `histAt` and `answered` must be defined on op positions and translated through
    `committedLb`.
  - Restate it, so that 2c's and 3a's integration does not inherit an unrealizable picture.
- **S4. The apply specs omit `srvStarted`.** `applyAll`, `applyEntries`, `apply` and
  `applyEntryNormal` take only `srvNode`, but the code uses `start`'s fields:
  - `applyWait` (`server.go:985`);
  - `w` (`1957`, `2009`);
  - `stopping` (`997`);
  - the wait group (`GoAttach`, `2017`).
  - `applyAll` also calls `sendMergedSnap`, whose spec requires `srvStarted s γ id`, and
    `applyThread` has no `id`.
  - Add `srvStarted` to those pres (`run` has it).
- **S5. Wrong statements in the sketches.**
  - `run.spec` says "`errorc` is never sent on". `applyEntries` starts `go s.stopWithDelay`
    (`server.go:1232`) when a conf change removes this member. It is a plain goroutine, not an
    attached one, and it sends on `errorc`, not on `stop` (`server.go:1350-1357`), while
    `applyEntries.spec` says "attached ... sends the stop request".
  - The spec still holds: the arm returns into the same deferred shutdown (`server.go:845-848`).
    But `errorc`'s protocol must carry an error value for `zap.Error`, and the sketch must say
    so.
- **S6. `applyConfChange.spec`'s decision claim is incomplete.**
  - Validation also reads the member-local `c.maxLearners` (`cluster.go:350-353`): cite 2e's Q5
    premise.
  - An accepted `RemoveNode` of the last voter makes raft panic. `confDecide` needs
    `d.step m = some m'`, and validation does not check for the last voter.
  - `nonissues/raft-remove-last-voter-panic.md` relies on `mayRemoveMember` at proposal time. That
    check runs on the proposer's view and can race with a concurrent removal: two removals, each
    validated against the same 2-voter view.
  - *Uncertain.* The second removal must then be accepted by a removed leader still leading,
    which needs raft's `StepDownOnRemoval` off. The spec needs a named source (premise or scope)
    for "accepted changes apply", and the nonissue should be re-examined.
- **S7. `cindex/Api.lean` says `ciState` is kept in both the apply thread's state and the batch
  transaction's lock invariant.** It is exclusive, so it can be kept in only one place. The
  realization must be one invariant (the hook's `UnsafeSave` reads it concurrently from the
  backend's commit goroutine), with an agreement half held with `ciWriter`.
  - The request `req/go_etcd_io_etcd_server_v3_storage.md` "from 2d" item 4 ("saved ... with the
    consistent index of the same entry") is false (see "What is good"). It is harmless; fix the
    text.
- **S8. `applyThread`'s realization says "`max p.appliedi ci`".** It is always `ci` (see "What is
  good"). Saying so simplifies `snapshot`'s and `createMergedSnapshotMessage`'s sketches
  (`c ≥ appliedi`).
- **S9. `revokeExpiredLeases` needs `⌜γ.cfg.leaseExpiry⌝` per receive.** `run` can call the
  spec only if 3c's expiry channel protocol carries `⌜γ.cfg.leaseExpiry = true⌝` with each
  receive (requested in `req/...lease.md`). With `leaseExpiry = false`, the lessor's channel is a
  trusted statement about time; record it in the trust note of K2.

## Snippets: proof outlines (where not already a finding)

- `ReqWriteAnswered`:
  - `Register`, then `raftNode.Propose.spec` with the update `histPropose` builds (`D := (· =
    data)`);
  - the receive gives `P id x`;
  - `x ≠ nil` comes from `P` (only the requester triggers `nil`; the apply triggers only
    `*apply.Result` for a normal entry with `answered`);
  - the type assertion is `P`'s, given the kind recorded at registration.
  - Provable once F1 (whose `mc`) and F2 (`run`'s chain) are fixed.
- `ReqPropose`, `ReqProcess`, `ReqReadIndex`: provable. They use `propErr`/`nodeErr`, and
  Perennial's context spec for `ctx.Err() ≠ nil` from `ctxDone`.
- `ReqWriteBeforeSend`: provable with the `Ready`'s `readyGot` in hand (`readyCheck` for the
  leader, `readyEnter` at 2e's `Save` for a follower).
- `ReqInstallSnapshot`, `ReqReplayBelowCI`: provable in-package once F3/F4 settle the image's
  point.
- `ReqNoSpaceAlarm`: as `ReqWriteAnswered`.
- `cindex` (3) and `schedule` (3): provable (see "What is good").

## Targets ranked by need of revision

1. `ApiApply.lean`, the laws and vocabulary: F1, F2, F3 (`snapImage_point`), F4, F7, S1-S3.
2. `raftNode.start.spec` and `applySnapshot.spec`: F3, F4.
3. `applyAll.spec` and `createMergedSnapshotMessage.spec`: F5, with R1's term bound.
4. The snippets `apply.go`, `snapshot.go`, `restart.go`: F6, F7, F8, F9.
5. `run.spec`, `applyEntries.spec`, `applyEntryNormal.spec`, `apply.spec`: F2, S4, S5.
6. `applyConfChange.spec`: S6.
7. `cindex/`: S7.
8. `schedule/`: none.

## Verdict

Not done. The scheme is sound in outline and needs none of R2d'a's premises. But there are
first-tier gaps:
- the proposer's configuration in the history (F1);
- the batches' order at `applyc` (F2);
- the ownership of `nodeConf` against the loop's unsynchronized `Advance` and the snapshot's
  configuration point (F3, F4);
- R1's missing term bound (F5);
- four snippets that are false or unprovable as stated (F6-F9).

All are repairable within the design. F5 needs R1. F1 needs a decision with W0 and 3a, the
author's open question 2. A second round is needed.
