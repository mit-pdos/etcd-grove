# R1 (raft's node API): completeness review, round 1

Reviewer: completeness, independent of the author. Read: `Spec/go_etcd_io/raft/v3/{Model,Api}.lean`
and the function specs that clients call (`StartNode`, `RestartNode`, `node__*`, `MemoryStorage__*`,
`MustSync`, `IsEmpty*`), the snippets `examples/specreq/raftnode/*.go` (`go vet` clean), the pinned
Go sources (`.lake/src/{server,raft}`), the examples (`examples/raft/{kv,kvreconf,kvdurable,kvfile}`;
`examples/lib/*` start etcd servers and do not call raft; `kvwitness` is the `RaftWitness/` tree,
which this branch deletes), and the old notes (`specs-ref`). I read the author's report only after
I had my findings. Line numbers are in the pinned sources under `.lake/src/`.

## Users and patterns

Every non-test use of `go.etcd.io/raft/v3` in `.lake/src/server` (bootstrap, raft, server,
v3_server, read, snapshot_merge, rafthttp, membership, wal, storage, zap_raft) and in the examples,
grouped:

| # | pattern (what the caller relies on) | example call site | snippet | verdict |
|---|---|---|---|---|
| P1 | proposal, one-shot credit; error is a node error or dropped | `etcdserver/v3_server.go:1114` | `ReqProposeOnce` | covered |
| P2 | proposal retried; duplicates deduplicated at apply | `examples/raft/kvdurable/kv.go:776` | `ReqProposeRetry` | covered |
| P3 | apply decodes **every** committed entry: a non-empty normal entry is some client's proposal (`MustUnmarshalMessage`, header panic), and only `EntryNormal`/`EntryConfChange` occur | `etcdserver/apply/apply.go:29-36`, `etcdserver/server.go:1958-1962` | none | **F2** |
| P4 | conf change proposed (v1; v2 joint in the examples), decided once cluster-wide, applied or refused (`NodeId = 0`, or not applied) | `server.go:1785`, `server.go:2034-2053` | `confchange.go` | covered |
| P5 | conf entries replayed below the consistent index are **not** passed to `ApplyConfChange` | `server.go:1934-1951`, `2052` | none | **F1** |
| P6 | linearizable read: fresh context per attempt, read state forwarded (only the last), answered after applying to its index | `etcdserver/read/read.go:236`, `raft.go:211-218` | `ReqLinearizableRead` | covered |
| P7 | Ready loop: leader sends before the write; enter at the WAL `Save`; MemoryStorage writes after it; Advance after the batch's conf changes | `raft.go:189-345` | `ReqReadyLoop` | covered, but see S1 |
| P8 | Ready loop split across goroutines: committed entries handed to the apply thread **before** `Save`; conf changes applied by that thread, handed back through `notifyc` before `Advance` | `raft.go:226-243`, `server.go:984-1002` | none | S1 |
| P9 | durability decision (`MustSync`) in the client and in the WAL (on WAL-owned hard states) | `kvdurable/kv.go:465`, `storage/wal/wal.go:1037-1047` | `ReqMustSync` | covered; S3 |
| P10 | snapshot made at the applied index with the server's `confState`, compaction below it | `server.go:2132`, `2180` | `ReqSnapshotCompact` | covered except during replay: **F3** |
| P11 | merged `MsgSnap` (snapshot replaced, data elsewhere), `ReportSnapshot` | `snapshot_merge.go:32-53`, `rafthttp/snapshot_sender.go:118-128` | `ReqSendSnapshot` | covered |
| P12 | snapshot received and installed | `raft.go:255-288`, `server.go:1021-1175` | `ReqReadyLoop` | covered |
| P13 | **reading an attached storage** (`Snapshot`, `FirstIndex`, `LastIndex`, `Entries`) | `server.go:755` (+ the panic guard `803-812`), `kvdurable/kv.go:606`, `kvreconf/kv.go:493`, `kvreconf/cluster.go:438-441`, `kvdurable/cluster.go:527-530`, `kvfile/storage.go:72-76` | none | **F4** |
| P14 | fresh start (`StartNode`), join (`RestartNode`, empty storage), restart from WAL + snapshot (`RestartNode`, `Applied` 0, configuration from the backend) | `bootstrap.go:595-600`, `533-565`, `741-751`, `107-116` | `restart.go`, `ReqBootstrapFromWAL` | covered except **F1** |
| P15 | `--force-new-cluster`: the WAL's commit raised and conf entries manufactured outside raft | `bootstrap.go:628-648` | none | S4 |
| P16 | transport: `Process` → `Step` (after the `To`/removed checks), `ReportUnreachable`, `ReportSnapshot` | `server.go:701-731`, `rafthttp/peer.go:178-251`, `pipeline.go:110-123` | `transport.go` | covered |
| P17 | `Status`: values (`Lead`, `ID`) | `server.go:930`, `kvdurable/reconf.go:114` | `ReqDisrupt` | covered |
| P18 | `Status`: the `Progress` map read (range and index), and expvar's JSON | `server.go:1590-1606`, `raft.go:55-63` | none | **F5**; S5 |
| P19 | leader transfer, tick, campaign, forget leader | `server.go:1285`, `raft.go:163` | `ReqDisrupt` | covered |
| P20 | stop, then restart on a new storage | `raft.go:420`, `kvdurable/kv.go:379` | `ReqStopRestart` | covered, but the snippet is unprovable: **F6** |
| P21 | logger: `SetLogger`, the zap adapter as `Config.Logger` | `raft.go:138`, `bootstrap.go:590` | none | left to R2 (req item 6); fine |

## What is good

- The approved durable design is kept whole: one `readyEnter` (fired at the client's commit point)
  plus the persistent `readyCheck`. This serves etcd's ordering exactly: the leader's
  `processMessages` send happens before `Save` (`raft.go:246-250`), followers send after it, and
  read states are forwarded before the write (`raft.go:211-218`, via `readyCheck`). `Driver.role` is
  exactly etcd's `islead` (updated only on a non-nil `SoftState`).
- `readyGot` gives `committedLb γ dl` at once, not at entering. That is what lets etcd hand
  committed entries to the apply thread before the WAL `Save` (P8).
- `StorageHolds` with `wcommit` admits etcd's WAL. `Save` writes a commit-only hard state without
  fsync (`wal.go:1047-1067`), so a restart may present any commit in `[wcommit, commit]`.
- `isStorage` as a bundle over `(S, cf)` serves the examples' wrapper storages, whose
  `InitialState` returns the bootstrap configuration (`kv/kv.go:72`, `kvreconf/kv.go:274`,
  `kvdurable/storage.go:177`). It also serves etcd's restart, where `cf σ` is the backend's
  membership (`bootstrap.go:107-116`).
- The second case of `node.ApplyConfChange` (an entry below the view whose change is a no-op)
  serves etcd's re-delivered bootstrap `AddNode`s after `StartNode`. `applyChange_v1` with
  `nodeId = 0` serves etcd's refusal.
- `msgSent_replaceSnap` serves the merged snapshot, which etcd sends with no data
  (`snapshot_merge.go:43-50`). etcd's guard `m.Snapshot.Index ≤ ep.appliedi` (`server.go:1008`) is
  the law's index premise.
- `ConfigOk` matches `validate` (`raft.go:293-338`) and the size-limit panic. etcd's `raftConfig`
  (`bootstrap.go:580-592`) and every example's configuration meet it.

## First tier

### F1. `RestartNode`'s configuration point `a ≤ σ.hs.commit` is not establishable by etcd in a reachable state

**Principle:** Complete (a user not served); "Durability, crashes and restarts are inside the spec".

**Evidence.**
- At a restart etcd replaces the WAL snapshot's `ConfState` by the backend's membership at its
  consistent index `c` (`bootstrap.go:107-116`). Raft then restarts with the configuration at `c`.
- `c` can exceed the WAL's `HardState.Commit`, and etcd says so itself (`bootstrap.go:632-636`:
  "This can result in consistent_index > CommitIndex"). Two causes:
  - a commit-only hard state is written without fsync (`wal.go:1047`);
  - the apply thread gets the batch's committed entries before `Save` (`raft.go:240` before `264`),
    and with synchronous writes these may include entries not yet in the WAL
    (`nonissues/raft-committedentries-stable-storage-doc.md`).
- So a crash after a backend commit leaves `c > σ.hs.commit`, and possibly `c > σ.last`.
- The old notes record the same gap for a graceful stop after a merged-snapshot install, carried as
  a trusted premise "for R2s" (`specs-ref/notes/decisions.md:33174-33180`,
  `specs-ref/notes/restart-plan.md:2516-2523`).

**Why no workaround exists.** With a conf change in `(σ.hs.commit, c]`, `RestartNode.spec` cannot be
applied: no `a ≤ σ.hs.commit` has `confAt γ a m` for the backend's `m`. A lower `a` does not help
either. etcd never calls `ApplyConfChange` for a replayed entry at or below `c` (`server.go:1934`,
`2034`, `2052`: `ValidateConfigurationChange` returns nil when `!shouldApplyV3`, and the
`ApplyConfChange` call is skipped). So `node.Advance.spec`'s
`confSkipped γ st.delivered v.applied st.delivered.length` fails for those entries: they are decided
`apply`, not `skip`.

**Caller affected:** batch 2e (bootstrap at a restart) and 2d (`run`, `applyAll` after a restart).

**Fix.** Replace `a ≤ uint.nat σ.hs.commit` by what raft needs of a configuration ahead of its
local commit. A candidate is `confAt γ a m` alone (it already says the first `a` entries are
committed cluster-wide) with `a` unbounded by the storage. Raft then holds the tracker at a
committed configuration from its local future, and the replayed conf entries up to `a` are below
the view, which etcd does not apply. R2 would have to show raft's invariants survive a tracker
ahead of `committed`. If that is too much, keep the premise as a scope restriction that is marked
as such: list it in `RestartNode`'s Margin, file it (`nonissues/`, with the etcd lines above), and
put it to the user. The approved example names "`a ≤ commit`" as a scope restriction, but not that
etcd reaches its violation.

### F2. No law lets a client exclude a raft-made `EntryConfChangeV2` (auto-leave) from the committed log

**Principle:** Complete; "a predicate a client would have to unfold (a missing law)".

**Evidence.**
- etcd panics on any entry type but `EntryNormal`/`EntryConfChange` (`server.go:1958-1962`). It
  also panics when a non-empty normal entry does not decode or has no header
  (`apply/apply.go:29-36`).
- The second fact is derivable: keep an invariant over `committedOps` and use `committedOps_lb`.
- The first is not. `opsOf` drops empty V2 entries, and nothing in the API limits them to joint
  configurations. Raft appends one itself, but only when the tracker is joint with `AutoLeave`.
  ProposeConfChange's leader validation also refuses a leave-joint at a non-joint configuration
  (`DisableConfChangeValidation` off, `ConfigOk`).
- So etcd, which never proposes V2 and never enters a joint configuration, cannot prove the
  default arm unreachable.

**Caller affected:** 2d (`EtcdServer.apply`); no snippet covers P3.

**Fix.** Add a law, for example:

```lean
def committedLb_emptyV2.spec : Prop :=
  ∀ γ l k e m, l[k]? = some e → e.isEmptyV2 →
    committedLb γ l ∗ confAt γ k m ⊢ ⌜m.isJoint⌝
```

It is true of both sources: raft's auto-leave and a client's explicit leave, which validation lets
through only when joint. Add a snippet "apply never sees an unknown entry type when no client
proposes V2": a loop over `CommittedEntries` that panics on V2, given `confAt` facts of non-joint
configurations only.

### F3. etcd's in-memory snapshot during WAL replay cannot meet `stor_createSnapshot`'s `snapValid`

**Principle:** Complete. This may also be a Go-code finding (below).

**Evidence.**
- After a restart, `ep.confState` is the backend's membership at `c` (`server.go:803-807`, from
  `bootstrap.go:107-116`), and `ep.appliedi` is the WAL snapshot's index `s`.
- Replayed conf entries do not update `ep.confState` (`server.go:2052`).
- `shouldSnapshotToMemory` fires every `memorySnapshotCount = 100` entries (`server.go:112`). The
  replay `(s, c]` is normally up to `SnapshotCount` (10000) long. So
  `CreateSnapshot(appliedi, ep.confState, nil)` (`server.go:2132`) runs at an `appliedi ∈ (s, c)`
  with the configuration at `c`.
- Whenever a conf change lies in `(appliedi, c]`, `snap_make` cannot be applied
  (`s.conf.Is m` with `confAt γ appliedi m`), so neither can `stor_createSnapshot`.
- A disk snapshot (`toDisk`) writes the same configuration into the WAL's snapshot record.
- This needs no crash: a graceful restart with a member change in the last 10000 entries.

**Caller affected:** 2d (`snapshot`, `snapshotIfNeededAndCompactRaftLog`).

**Go code.** This looks like an etcd defect: a raft snapshot whose configuration is later than its
index. I found no consequence in etcd's own flow:
- raft's `MsgSnap` from this storage is replaced by the merged message, whose configuration is
  correct once the replay is over;
- a later restart rebuilds the configuration from the backend again.

So it is likely a `nonissues/` entry (no reachable wrong result found; etcd's merge masks it). It is
not in `specs-ref/issues` or `nonissues`. The author, or 2d, should file it with this analysis.

**Fix (spec side).** Either:
- R1 states what raft tolerates of a stored snapshot's configuration: any configuration at an index
  in `[s.index, applied]`, which raft only sends and the receiver restores. That is a raft-proof
  question (R2) and may be false of raft's own `MsgSnap` path.
- Or 2d excludes snapshots during replay with a premise, filed as a scope restriction.

Either way, put it to the user.

### F4. No law reads an attached storage

**Principle:** Complete; a missing law.

**Evidence.**
- Once a node starts, raft holds `S σ` in its invariant (`StartNode`/`RestartNode` take `S σ` and
  do not return it).
- The only laws giving an update over `S` are writes: `readyStor_install`, `readyStor_append`,
  `stor_compact`, `stor_createSnapshot`, `stor_setHardState`.
- Every user reads the attached storage:
  - etcd's `run()`: `s.r.raftStorage.Snapshot()` (`server.go:755`). It relies on the result: it
    panics on a nil `ConfState` (`803-812`) and seeds `ep.{confState, appliedi, appliedt,
    *SnapshotIndex}` from it, the values every later `CreateSnapshot`/merge depends on.
  - kvdurable and kvreconf: `FirstIndex()` to choose the compaction point (`kvdurable/kv.go:606`,
    `kvreconf/kv.go:493`), and their status dumps (`FirstIndex`, `LastIndex`, `Snapshot`).
  - kvfile: `Encode` reads the whole storage, `InitialState` included, to persist it
    (`kvfile/storage.go:72-76`).
- None of these can be verified: the `MemoryStorage` specs fire on `memStor ms σ`, which the client
  no longer has. No snippet covers P13.

**Fix.**
1. Add `stor_read.spec : nodeStorage n γ S ⊢ AU <{ ∃∃ σ, S σ }> @ ⊤ \ ↑γ.ns, ∅ <{ S σ, COMM ⌜R σ⌝ }>`,
   with the facts raft's invariant keeps that clients need: the stored snapshot is the start's
   or `snapValid` (etcd's `ep` seeding), and the compaction point is at most the applied index.
2. Add a snippet `ReqReadAttached`: `Snapshot()` after `RestartNode`, with a panic if its index
   differs from the start's stored snapshot when no `Ready` has been handled. Also `FirstIndex()`
   bounding a compaction.
3. `InitialState` is non-atomic (`nonissues/raft-memorystorage-initialstate-unlocked.md`), so
   kvfile's attached-storage `InitialState` needs either an atomic variant over `S` or an explicit
   exclusion.

### F5. `statusOwn` has no law: etcd cannot read a `Status`'s `Progress` map

**Principle:** Complete; a missing law (the client would have to unfold `statusOwn`).

**Evidence.** `isLearnerReady` (`server.go:1590-1606`):
- tests `rs.Progress == nil` (a value comparison, fine);
- ranges over `rs.Progress` and indexes `rs.Progress[leaderID]` (both need the map's points-to);
- reads `progress.Match`.

`node.Status.spec` gives only the opaque `statusOwn s` and `ID`. No law turns `statusOwn` into map
ownership. The R4 req note says what `statusOwn` stands for, but clients get nothing.

**Caller affected:** 2e or 2c (`isLearnerReady`, `PromoteMember`).

**Fix.** Add `statusOwn_progress.spec : statusOwn s ⊢ ∃ pm, ownMap s.Progress' (DFrac.own 1) pm ∗ …`
(Perennial's map ownership; values are `tracker.Progress` structs, with `Inflights` a fresh clone).
Add a one-line snippet: range over `Status().Progress`.

### F6. `ReqStopRestart` calls `Stop` twice, which no spec allows

**Principle:** a snippet unprovable (the brief's first tier).

**Evidence.** `node.Stop.spec` takes `nodeRunning n 1`. After the first `Stop` the client holds
`nodeStopped n`, and `exclusive.spec` gives `nodeRunning ∗ nodeStopped ⊢ False`. The spec's Margin
says this. No user calls `Stop` twice: etcd's `onStop` calls it once (`raft.go:420`), the examples
once.

**Fix.** Drop the second `Stop` from the snippet. Or, if a user is found, generalize the pre to
`nodeRunning n 1 ∨ nodeStopped n`, giving `nodeStopped n` back, and the vacancy only in the first
case.

## Second tier

- **S1. The concurrent Ready/apply split (P8) has no snippet.** `ReqReadyLoop` applies after the
  write in one goroutine. etcd applies committed entries in another goroutine, before `Save`. The
  `nodeConf` token goes to the apply thread with a conf batch and comes back through the second
  `notifyc` send before `Advance` (`raft.go:300-341`, `server.go:984-997`). Non-conf batches are
  `Advance`d while their entries may still be applying. The specs allow all of this (`committedLb`
  at receive; `Advance` needs nothing from the application). A snippet with an apply goroutine and
  a channel hand-off of the conf entries would pin down that reliance.
- **S2. `MemoryStorage.Entries.spec` requires `lo < hi`; Go accepts `lo = hi`** (an empty slice, or
  `ErrUnavailable`: `storage.go:145-166`). kvfile's `Encode` calls `Entries(first, last+1, ^0)` on a
  storage with no entries after its snapshot (`kvfile/storage.go:76`). The spec also only gives a
  non-empty prefix, while kvfile relies on getting every entry with `maxSize = 2^64-1` (it persists
  the whole log). Relax to `lo ≤ hi`, and state the full range when the size limit is not reached
  (`limitSize` returns everything when the total fits). The `isStorage` contract can keep `lo < hi`:
  raft never asks for an empty range.
- **S3. `MustSync`/`IsEmptyHardState` take `hsPtr` at `DFrac.discard`.** The WAL calls them on its
  own `w.state` (`wal.go:1023-1047`), fresh or cloned (`wal.go:602`) and never mutated afterwards,
  so it can discard it. A spec over any `dq`, given back, is stronger and costs nothing.
- **S4. `--force-new-cluster` (P15) is out of scope but not said.** etcd raises the WAL's commit to
  the consistent index and appends manufactured conf entries as committed (`bootstrap.go:628-648`,
  `storage/util.go:34-95`), which no `raftState`/`committedLb` history admits. Say so in
  `RestartNode`'s Margin (a disaster-recovery mode outside the protocol), so 2e does not search for
  a way.
- **S5. expvar `raft.status`** (`raft.go:55-63`) JSON-marshals a `Status` (`Status.MarshalJSON`,
  left out by the author) from any goroutine at any time. Fine as a recorded omission. Note that it
  calls `n.Status` after `Stop` too, which `node.Status.spec` already allows.
- **S6. Crash without `Stop`.** `nodeVacant` comes back only from `node.Stop` (or `rawNode_drop`).
  For a process crash (etcd's real restart, as opposed to the examples' simulated `Stop`), no law or
  crash rule re-creates `nodeVacant γ id`, which `RestartNode` takes. Uncertain whether this belongs
  in R1 (a crash law) or in the adequacy/crash model. The approved design does not discuss it;
  worth an open question.
- **S7. `Status` says nothing of `Lead`.** etcd uses `raftStatus().Lead == self` in
  `ensureLeadership` (`server.go:912-937`) to gate lease revocation, checkpoints and renewals. These
  are heuristics; the operations go through raft, except `LeaseRenew`, whose correctness is
  time-based. Acceptable if 3c and 2c state nothing that needs "was leader". If they do, a
  persistent "node `id` led term `t`" fact in the post is true and cheap.
- **S8. Uncertain: one-shot credits over rafthttp.** I did not establish that rafthttp delivers a
  `MsgProp` at most once (stream vs. pipeline; no retries seen in `pipeline.go:90-130`). etcd's
  `γ.dup = false` rests on it. 2f should confirm.
- **S9. Coverage note.** No snippet shows `configure`'s reliance on the committed conf entry
  decoding to the proposed change, `Id` included (`server.go:1785-1800`, `1951-1955`). It is
  derivable from `node.ProposeConfChange.spec`'s `decodeConfChange` and the `committedOps`
  invariant. A two-line addition to `ReqApplyOrRefuse` (panic if the decoded `Id` differs from the
  proposed one, for the proposer's own entry) would record it.

## Establishability spot checks (one site per covered pattern)

- **P1** `v3_server.go:1114`: `isNode` from the `raftNode`'s invariant. `cctx` is a
  `context.WithTimeout`. `data` is a fresh `proto.Marshal`, discardable. The update is one-shot.
  The post's `propErr` matches the error mapping at `v3_server.go:1115-1120`. OK.
- **P6** `read.go:236`: `ReadIndex(cctx, 8-byte id)` with a context from
  `context.WithTimeout(Background())`; the id is registered fresh (`readCtx_register`, freshness
  from the trusted id generator, `specs-ref/nonissues/etcd-request-id-restart-reuse.md`). The read
  state reaches the read loop through `readStateC` with its persistent `readState`. OK.
- **P7** `raft.go:189-345`:
  - the receive is in a `select` with ticker and stopped (`readyChan_recv` as `recvAu`);
  - the leader send uses `readyCheck`, enter at `Save` (`raft.go:264`);
  - `ApplySnapshot` (error ignored) is legitimate by `readyStor_install`'s raft-guaranteed pre;
  - `Append` (`readyStor_append`), then `Advance` with `readyStor n none k []`.

  etcd never calls `SetHardState` on the attached storage; fine. OK.
- **P10** `server.go:2132`, `2180`: `appliedLb` from `Advance` (the apply thread waits for
  `raftAdvancedC`, `server.go:997`). `storSnapLb` comes from `stor_createSnapshot`'s COMM even on
  `ErrSnapOutOfDate`, after which etcd still compacts. OK, except during replay (F3).
- **P11** `snapshot_merge.go`: `snapValid` of `(appliedi, appliedt, confState, [])` by `snap_make`,
  from the apply thread's `snapsMade` and its `confAt`. Then `msgSent_replaceSnap`. OK.
- **P14** fresh start `bootstrap.go:599`:
  - `BootLog` of the sorted members with their JSON contexts, the same at every founder given the
    same `--initial-cluster`;
  - the empty storage from `bwal.MemoryStorage()`;
  - re-delivered bootstrap `AddNode`s validated and applied as no-ops (second case of
    `ApplyConfChange`).

  Join (`bootstrap.go:533`, no peers): `confAt γ 0 Membership.empty` from `cluster_alloc`. OK.
  Restart: OK when `c ≤ σ.hs.commit`, else F1.
- **P16** `server.go:701-722`: `m.to = id` by the `MemberID() != To` check; `msgPts` own (a fresh
  decode, `rafthttp/http.go:148`, `307`); `msgSent`/credit travel with the bytes (2f/3h's
  round-trip req). `context.TODO()` (`http.go:148`) needs `context.isContext`. I assume Perennial's
  `Background` model covers `TODO` (not checked).
- **P20** `raft.go:420`: `onStop` runs in the Ready goroutine, which holds `nodeRunning n 1`
  (`readyEnter` takes and returns a fraction). OK.

## Ranking (need of revision)

1. `RestartNode.spec` (F1).
2. `Api.lean`'s storage laws: a read law (F4), and `stor_createSnapshot`/`snap_make` at replay
   (F3, with the user).
3. `Api.lean`'s committed-log laws: the empty-V2 law (F2).
4. `node.Status.spec` / `statusOwn` (F5).
5. Snippets: `ReqStopRestart` (F6); new ones for P3, P8, P13.
6. `MemoryStorage.Entries.spec` (S2), `MustSync`/`IsEmptyHardState` (S3), Margins of
   `RestartNode` (S4).
7. The rest (`node.Propose`, `ReadIndex`, `Step`, `ProposeConfChange`, `ApplyConfChange`,
   `Advance`, `Ready`, `readyChan_recv`, `StartNode`, the MemoryStorage writes): no revision needed
   for completeness.

## Verdict

The Ready/durability design, proposals, reads, conf changes on a running cluster, transport and the
merged snapshot serve every user I found. The batch is not done: four users are not served.
- etcd's restart, whose configuration is ahead of the WAL commit (F1).
- etcd's apply loop's entry-type panic (F2).
- etcd's snapshots during replay (F3), which may need a user decision.
- Every reader of an attached storage (F4).

Add the missing `Status` law (F5) and fix the unprovable snippet (F6); then a second round on F1-F4.
