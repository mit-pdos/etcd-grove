# A4 (raft node API and core, batches R1, R2): completeness verification

Reviewer: completeness kind, independent. Commit under review: `1aa6fc1337` (`specs-only`).
Targets: `SpecPlan/Spec/go_etcd_io/raft/v3/{Model,Api,ApiCore}.lean` and the node / `RawNode` / `MemoryStorage` /
`raft.go` specs beside them (172 files at the top level of `SpecPlan/Spec/go_etcd_io/raft/v3/`, not counting
R3's `raftLog__*`, `unstable__*`, `readOnly__*`, `ApiLog`); snippets `examples/specreq/{raftnode,raftcore}/`.
I wrote the findings below before I read `batch-R*.md`, `integration-*.md`, `open-questions.md`
and `reviews/`. I read those only afterwards, to mark which findings are already recorded.

## Verdicts

| batch | verdict |
|---|---|
| **R1** (node API: `node`, `RawNode`, `MemoryStorage`, `Storage`, `Ready`, `Config`, starts) | **FAIL**: F1, F2, F3 (first tier); F4 (coverage, second tier) |
| **R2** (raft core: `raft.Step`, `step*`, `become*`, the `Ready` phases, tracing, loggers) | **PASS WITH OPEN DECISIONS**: the term/index receipt bound at `cluster_alloc` (open-questions 2.3/5.1; R1 Q9, R2 Q1); `ConfigOk`'s scope and `MaxInflightMsgs ≤ 2^62` (2.1, 2.2). R2's `logger.go` laws are where F3's missing law most naturally goes. |

Counts:
- **Specs checked against their users:** all 172 R1/R2 files, plus the 63 laws in `Api.lean` and the 25 in `ApiCore.lean`.
- **Snippets checked against the users:** 22. That is 7 files in `raftnode` (14 REQs) and 4 in `raftcore` (13 REQs, counted with R2's own callers).
- **User call sites checked:** about 45, in 24 patterns. 20 patterns close; the 4 that do not are below.
- **Old-tree coverage:** every old spec of `Spec/go_etcd_io/raft/v3/` has one here except 2 (F4).

## The users, by pattern

These are etcd at `a4d2bb17` (`.lake/src/server`) and the examples (`examples/raft/{kv,kvdurable,kvreconf,kvfile}`). `RawNode` is used only in `_test.go` files, so its callers are raft's own `node.run`.

| # | pattern | sites | specs used | closes? |
|---|---|---|---|---|
| U1 | start a new member with peers | `bootstrap.go:599` (peers from `:546-553`) | `StartNode`, `cluster_alloc`, `BootLog` | **no: F2 (`peersPts`), F3 (`loggerOk`)** |
| U2 | restart from WAL or file; join with empty storage | `bootstrap.go:597`, `:741-753`; `kvdurable/cluster.go:216`; `kv/cluster.go:150` | `RestartNode`, `NewMemoryStorage`, `MemoryStorage.{ApplySnapshot,SetHardState,Append}`, `freshIds_take` | yes, except F3. Checked: etcd's snapshot `ConfState` replaced by the backend's (`bootstrap.go:107-116`) fits `max off Applied ≤ a`, `(cf σ).Is m`, `snapValid` through `snap_make` at `a ≥ index`. kvdurable's random `Applied ∈ [first-1, index]` fits the `Applied` premise. |
| U3 | custom `Storage` wrappers (`InitialState` with a fixed configuration, `Snapshot` returning `ErrSnapshotTemporarilyUnavailable`) | `kv/kv.go:72-84`, `kvdurable/storage.go:177-191`, `kvreconf/kv.go:274-283`, `kvfile/storage.go:23-38` | `isStorage` (a transparent bundle), the `MemoryStorage.*` specs | yes. `kv`'s constant empty `HardState` needs the client's `S` to pin `σ.hs`; `kv` never calls `SetHardState`. |
| U4 | `Ready` receive in a `select` with the ticker and stop | `raft.go:186-189`, `kvdurable/kv.go:440-446` | `node.Ready`, `readyChan_recv` (Perennial's select takes a `[∧list]` of clause pres, so `nodeDriver` may be used in the `Ready` clause alone) | yes |
| U5 | read the `Ready`'s soft state and read states | `raft.go:191-213` (`rd.SoftState.Lead`, `rd.RaftState`, `rd.ReadStates[len-1]`), `read.go:166-177` (`rs.RequestCtx`, `rs.Index`), `kvdurable/kv.go:452-453`, `:741-749`, `kv/kv.go:279`, `kvreconf/kv.go:401` | `readyOwn`'s `softStateOpt`, `readStatesRO` | **no: F2** |
| U6 | the leader sends before its write, the others after | `raft.go:228-232`, `:296-309`; `kvdurable/kv.go:488-499` | `readyCheck` (gated on `(b.soft.map (·.2)).getD st.role`, the same thing as etcd's `islead`), `readyEnter` | yes |
| U7 | write the batch: snapshot, hard state, entries | `raft.go:250-292`; `kvdurable/kv.go:466-474`; `kvreconf/kv.go:390-397` | `readyStor_install`/`_append`, `stor_setHardState`, `MemoryStorage.*` (the client's update with a precondition implies the method's unguarded one) | yes |
| U8 | durability policy | `kvdurable/kv.go:464-465`, `wal.go:1023-1047` | `MustSync`, `IsEmptyHardState`, `IsEmptySnap`, `Durable.next`'s `wcommit` | yes |
| U9 | apply conf changes before `Advance`, refuse by `NodeId = 0` or by not calling | `server.go:2032-2053` (refusal only when `shouldApplyV3`, `cluster.go:307`); `raft.go:294-338`; `kvdurable/kv.go:700` | `node.ApplyConfChange`, `confDecide`, `confSkipped`, `node.Advance` | yes. The bootstrap entries re-applied as no-ops fall in the below-the-view case. |
| U10 | `Advance`, then publish the applied index | `raft.go:343-350`; `kvdurable/kv.go:511-516` | `node.Advance` (the stop disjunct is excluded by the loop's `nodeRunning` share) | yes |
| U11 | snapshot and compaction after `Advance` | `server.go:2132`, `:2180` (after `raftAdvancedC`, `server.go:997`) | `stor_createSnapshot`, `stor_compact`, `snap_make`. Either result of `CreateSnapshot` gives `storSnapLb`. | yes |
| U12 | **snapshot of a delivered entry before `Advance`** (requested mid-batch, taken by a concurrent goroutine) | `kvdurable/kv.go:504-508` → `:590`; `kvreconf/kv.go:402-406` → `:480` | `stor_createSnapshot` | **no: F1** |
| U13 | compaction from `FirstIndex` up to the known snapshot | `kvdurable/kv.go:606-613`, `kvreconf/kv.go:493-` | `MemoryStorage.FirstIndex`, `stor_read`, `stor_compact` | yes |
| U14 | read the attached storage at start | `server.go:755` | `stor_read`, `MemoryStorage.Snapshot` | yes |
| U15 | propose: one-shot (etcd), or retried with persistent credits (examples) | `v3_server.go:1114`; `kvdurable/kv.go:776` | `node.Propose`, `propErr`; the server's `histPropose` (binders `∀∀ t bs` instantiate to `node.Propose`'s `∀∀ t`) | yes |
| U16 | propose a conf change | `server.go:1785`; `kvdurable/reconf.go:90` | `node.ProposeConfChange` (the `wireBound` premise is 3h's open question 3) | yes, with that decision open |
| U17 | linearizable read | `read.go:236`; `kvdurable/kv.go:811` | `readCtx_register`, `node.ReadIndex`, `readState_fire`, `readState_registered` | yes, given F2 for reading the state |
| U18 | transport: step, report unreachable, report snapshot | `server.go:721`, `:726`, `:731`; rafthttp `peer.go:249-251`, `pipeline.go:110-123`, `stream.go:236,337`, `snapshot_sender.go:118-128`; `kvdurable/cluster.go:381-415` (steps `copyMsg` copies: `send` copies at `:318-322`); `kv/cluster.go:123`; `kvfile/cluster.go:133` (`proto.Clone`) | `node.Step` (`msgRecv`), `node.ReportUnreachable`, `node.ReportSnapshot` | yes |
| U19 | merged snapshot message | `server.go:1001-1006`, `snapshot_merge.go` | `msgSent_replaceSnap`, `msgSent_snapTerm`, `BatchOk`'s term bound | yes |
| U20 | ticks from any goroutine | `raft.go:161-166`, `advanceTicks`; `kvdurable/kv.go:360` | `node.Tick` | yes |
| U21 | status: the expvar method value, `Lead`, the learner check | `bootstrap.go:601-603`, `raft.go:62`; `server.go:930`, `:1590-1606`, `:2471` | `node.Status`, `statusOwn_progress`, `Status.MarshalJSON` | yes |
| U22 | disruptions | `server.go:1285`; `kvdurable/reconf.go:110-118` | `node.{TransferLeadership,Campaign,ForgetLeader}` | yes |
| U23 | stop, crash and restart | `raft.go:420-438`; `kvdurable/kv.go:369-393` | `node.Stop`, `RestartNode` on a new storage, `raftState_crash` (scope `crashScope`: open-questions 2.8) | yes, with that decision open |
| U24 | **loggers**: the package logger and `Config.Logger` | `raft.go:138` (`raft.SetLogger`), `bootstrap.go:591` (`NewRaftLoggerZap`); `kv/cluster.go:157`, `kvreconf/cluster.go:159`, kvdurable's `quietLogger{}` | `SetLogger`, `StartNode`/`RestartNode`'s `loggerOk cv.Logger'` | **no: F3** |

R2's users are R1's own proofs. I checked:
- `node.run` (`node.go:343-446`) against `RawNode.HasReady` (with `readyKept`), `readyWithoutAccept`, `readyFresh_ro`/`raftRO_peek` (the reads of `lead`, `Term`, `id`, `logger` and `trk.Progress`), `ready_handout`, `acceptReady`, `RawNode.Advance`/`rawNodeAt_advance`, and `raft.applyConfChange` in the `confc` arm.
- `raft.Step`'s `stepIn` against each source: `node.Propose` (`From` rewritten to `r.id`); a forwarded `MsgProp` through `propc`; `node.ReadIndex` (`From` 0, one entry); the reports (`MsgUnreachable` and `MsgSnapStatus` from a peer id, `MsgTransferLeader` from the transferee); and received messages (`msgRecv`).
- `RawNode.Bootstrap` (`bootstrap.go:32-81`) against `rawNodeAt_bootstrap` and `raft.applyConfChange`. The context-less `AddNode` agrees with the decided change through `∀ mm, applyChange (.v2 c2) mm = applyChange c mm`.

All of these close.

## First-tier findings

### F1. A snapshot of a delivered but not yet `Advance`d entry is not served (kvdurable, kvreconf), a regression from the verified old proofs

- **Principles:** Complete (every caller); "A smaller API is not a narrower scope" (the old spec served this pattern, and kvdurable's old proof, `Replica__snapshot.lean`, uses it with no `sorry`).
- **Evidence.**
  - Both examples request a snapshot from inside the committed-entries loop, before `Advance`: `kvdurable/kv.go:504-508` (`r.request(snapIndex, true, 0)` right after `applyEntry(e)`, `r.index = e.GetIndex()` at `:681`); `kvreconf/kv.go:402-406`.
  - Their snapshotter goroutine then calls `CreateSnapshot(req.index, …)` concurrently (`kvdurable/kv.go:590`, `kvreconf/kv.go:480`).
  - The entry is in the `MemoryStorage`, because the batch's entries were appended before applying (`kvdurable/kv.go:474`, `kvreconf/kv.go:397`), so Go does not panic.
  - On an attached storage, the only source of the client's update is `stor_createSnapshot.spec` (`Api.lean:898`), which takes `appliedLb n (uint.nat s.index)`.
  - `appliedLb` is produced only by the starts and by `Advance` (`node__Advance.lean:58`, `ApiCore.lean:535`). So at `index = e.index`, which is past the last `Advance`, the premise has no source.
  - The old `MemoryStorage.CreateSnapshot.spec` (`specs-ref`) took `J.DL i` (the delivered prefix reaching `i`) and the frozen stored entry (`memLog γs i [e]`). It did not take the applied index.
  - The snippet hides the gap: `ReqSnapshotCompact` (`examples/specreq/raftnode/storage.go:74-83`) lists `kvdurable/kv.go:585-620` as a user but assumes "at most n's applied index (appliedLb)", which kvdurable does not meet.
- **Callers affected:** `examples/raft/kvdurable` and `examples/raft/kvreconf` (`Replica.snapshot`). etcd is not affected: it snapshots only after `raftAdvancedC` (`server.go:990-1000`).
- **Restatement.**
  1. Add a persistent `storedLb n i`: entries `1..i` are committed, delivered, and in the attached storage. Produce it from `readyStor_append.spec`'s COMM, for `i ≤ min |dl| (k + |es| - 1)`, with `dl` the batch's delivered log. That needs `dl` in `readyStor`, or a `deliveredLb` premise.
  2. Add a law `appliedLb n i ⊢ storedLb n i`.
  3. Have `stor_createSnapshot` take `storedLb n s.index` instead of `appliedLb`. `stor_compact` keeps `appliedLb`, which the fork's `raftAdvancedC` comment explains: compacting past raft's applied index panics an election.
  4. Add a snippet `ReqSnapshotMidBatch`.

  Alternatively, if the author holds that raft needs the applied floor (R3's `logFloor`) for the term tie, state why. Then kvdurable and kvreconf must change their Go code, and the old proof's coverage is lost: put that to the user.

### F2. The `Ready`'s soft state, its read states, and `StartNode`'s peers are opaque with no laws, so no client can read or build them

- **Principles:** "A client does not unfold the spec's definitions" (each such unfold is a missing law); Complete; "Law coverage".
- **Evidence.**
  - `softStateOpt`, `readStatesRO` and `peersPts` (`Api.lean:165`, `:168`, `:171`) are `opaque`. Their only law is persistence (`persistent.spec`).
  - Nothing outside R1's own files mentions them (grep over `SpecPlan/Spec/`). `integration-I2.md:44` lists them as "left", with no laws.
  - Clients that read the `Ready`:
    - etcd's `raftNode.start` reads `rd.SoftState != nil`, `rd.SoftState.Lead` and `rd.RaftState` (`raft.go:191-206`). It indexes `rd.ReadStates[len-1]` and sends the value (`:212-213`). The read loop then reads `rs.RequestCtx` (its length, and the big-endian decode) and `rs.Index` (`read.go:166-177`).
    - kvdurable reads `rd.SoftState.RaftState` (`kv.go:452-453`), and `rs.Index` and `rs.RequestCtx` in `answer` (`kv.go:745-749`).
  - A client that builds the peers: etcd's `bootstrapRaftFromCluster` makes `[]raft.Peer{ID, Context}` (`bootstrap.go:546-553`), but `StartNode.spec` requires `peersPts peers dq ps`, which nothing introduces.
  - The server's `raftNode.start` sketch (step 3: "the soft state into the ready handler; read states: … sent on `readStateC`") depends on these reads.
- **Callers affected:**
  - etcd: `raftNode.start` (2d), `Read.requestCurrentIndex` (the read loop), and `bootstrapRaftFromCluster`/`bootstrappedRaft.newRaftNode` (2e).
  - Every example's run loop.
- **Restatement.** Either make the three transparent definitions over Goose points-to (as `readyMsgsOwn`, `hsOpt` and `snapOpt` already are), or export these laws:
  - `softStateOpt_unfold`: `softStateOpt p o ⊣⊢ ⌜p = null ∧ o = none⌝ ∨ ∃ l r, ⌜o = some (l, r)⌝ ∗ p ↦□ SoftState.mk l r`.
  - `readStatesRO_unfold`: an `ownSlice sl rsv □` of `ReadState` values, each `RequestCtx ↦*□ c` with `Index = i`, pairwise with `rs`.
  - `peersPts_intro`: from `ownSlice sl vs dq` of `Peer` values whose `Context` slices are `↦*{dq} ctx`, giving `peersPts sl dq ps`.

  Add a snippet that reads `rd.SoftState.Lead` and `rd.ReadStates[len-1].RequestCtx`.

### F3. `loggerOk` has no introduction law, so no client logger can be passed to raft

- **Principles:** "Every premise has a source the client sees"; "Canonical specs … an interface value gets a bundle"; Complete.
- **Evidence.**
  - `loggerOk` (`Api.lean:419`) is opaque. Its docstring says "etcd's zap adapter and the examples' loggers meet it (their batches' laws)", but no such law exists. A grep for `loggerOk` outside `SpecPlan/Spec/go_etcd_io/raft/v3/` finds only a docstring in `newRaftNode.lean:10`. `NewRaftLoggerZap` has no spec, and zap's `Api.lean` mentions no raft.
  - The only introductions are `defaultLogger_loggerOk.spec` (`ApiCore.lean`, for `*DefaultLogger`) and `getLogger.spec`'s post.
  - Two premises need `loggerOk` of a client's logger:
    - `StartNode`/`RestartNode`/`NewRawNode`/`newRaft` take `⌜cv.Logger' = nil⌝ ∨ loggerOk cv.Logger'` (`StartNode.lean:64`, `RestartNode.lean:78`).
    - `SetLogger.spec` takes `loggerOk l`.
  - etcd passes its zap adapter to both (`bootstrap.go:591`, `raft.go:138`). The examples pass `quietLogger{}` (`kv/cluster.go:157`, `kvreconf/cluster.go:159`, kvdurable's `config`).
- **Callers affected:** every start in etcd and in the examples (U1, U2, U24), and etcd's `newRaftNode`.
- **Restatement.** Make `loggerOk lg` a transparent bundle, as `isStorage` is: for each of `Debug(f)`, `Info(f)`, `Warning(f)`, `Error(f)` on `lg`'s dynamic type and method table, `□ ∀ args Φ, ▷ Φ #() -∗ WP (method args) {{ Φ }}`; for `Fatal*`/`Panic*`, nothing, since raft calls them only on paths its premises exclude. Or keep it opaque and add `loggerOk_intro.spec` taking those triples. `loggerOk_nonnil` and `defaultLogger_loggerOk` (R2) then become provable from the bundle. Add a snippet with a client-defined logger (`ReqClientLogger`).

## Second-tier findings

- **F4 (coverage).** `MemoryStorage.firstIndex` and `MemoryStorage.lastIndex` (`storage.go:191-206`, lock-held helpers called by `Append`, `Entries`, `CreateSnapshot`, `Compact`, `FirstIndex` and `LastIndex`) had specs and linked proofs in the old tree (`specs-ref` `Link.lean:420-453`). They have no spec here, and the sketches of `MemoryStorage.{FirstIndex,LastIndex,Compact,CreateSnapshot,Append}` call them ("Under the lock, `firstIndex`"). This is the author's recorded choice (`batch-R1.md:117`), not a user decision. Under "A smaller API is not a narrower scope", restore the two internal specs (they mirror the code).
- **F5 (docstring).** `appliedLb`'s docstring (`Api.lean:297-301`) says it also covers "the index of a snapshot installed in its storage and not yet `Advance`d". No law produces that: `readyStor_install`'s COMM gives `storSnapLb`, not `appliedLb`. Either drop the clause, or make `readyStor_install` give `appliedLb n s.index` (harmless for `stor_compact`: at or below the stored snapshot).

## Open decisions that bear on these users (recorded; they still count)

- **Term/index receipt bound.** Missing from `cluster_alloc` (`Api.lean`'s docstring; open-questions 2.3/5.1). Without it, `raft.Step` and everything above it are unprovable. Every user's start is affected.
- **`crashScope`** (`confAboveOk`, no crash during a batch that carries a snapshot): open-questions 2.8. etcd's crash restarts are served only within it.
- **`ConfigOk`:** `ReadOnlySafe` only, synchronous storage writes, `MaxInflightMsgs ≤ 2^62` (2.1, 2.2). etcd and the examples meet all three.
- **`ProposeConfChange`'s `wireBound < 2^48`:** 3h's question 3. etcd's member contexts are bounded in practice, but no caller spec states it.
- **A storage is attached once** (2.4). Every user restarts on a new storage, so this costs nothing today.

## Not findings (checked)

- kvdurable steps copies, not raft's own messages (`send` calls `copyMsg` at `cluster.go:318-322`), so `msgRecv` holds.
- etcd's refused conf change with `NodeId = 0` is called only when `shouldApplyV3` (`cluster.go:307-309` returns nil otherwise), so `confDecided` agrees across a restart.
- etcd's leader branch waits for its conf changes before `Advance` (`raft.go:322-331`), so `nodeConf` comes back.
- `memStor_isStorage`'s `Term` needs `i < off + 2^63`, which a Go slice's length bound gives.

No bug in the Go code found; nothing for `issues/`.
