# Repair: group `raft-core` (raft/v3 top level; snippets raftnode, raftcore, raftlog)

Reports: `A4-raft-node-core-{provability,completeness}.md` (all), the R3 parts of
`A5-raft-log-conf-pb-{provability,completeness}.md`, and the coordinator's relay of raft-conf-pb's
requests. Files are under `Spec/go_etcd_io/raft/v3/` and `examples/specreq/` unless a path is given.

## A4 provability

- **P1, `BatchOk` is false for a snapshot followed by entries.** Fixed in `Model.lean`. With a
  snapshot, the clause now bounds `entsFrom` by `s.index + 1` instead of `durable.last + 1`.
  `Durable.next` already cut the log at the snapshot's base. I kept the reviewer's `≤`; equality
  holds in Go but nothing needs it.
- **P2(a), the crash law and `BatchOk` contradict each other.** Fixed in `Api.lean`
  (`raftState_crash`). The hard state left by a crash is now one whole record:
  - the old one: `D`'s term and vote, `wcommit ≤ c ≤ D.commit`;
  - or the batch's: its term and vote, `wcommit ≤ c ≤` the batch's commit.

  This matches `wal/Api.lean`'s `crashedMid` (both cases). The docstring says why the round-3
  mixture was wrong.
- **P2(b), the realistic crash leaves entries above the durable term.** Fixed in the header of
  `ApiCore.lean`:
  - item 1 now covers it: the node cannot win before that term, by quorum intersection across at
    most one conf entry above its commit;
  - item 4 (V2) states the durable invariant "at most one conf entry above `wcommit`".
- **P3, `node.Advance`'s post has no source.** Fixed, across R2 and R3.
  - **`ApiCore.lean`**:
    - `rawNodeAt_advance` is now the rendezvous. It takes the client's resources and gives R1's
      whole post at once (the driver, `appliedLb` at the delivered log, the view wand), leaving
      the new `rawNodeAdv`.
    - The new `rawNodeAdv_open` releases the acknowledgements (`ackOk`). Its closing gives
      `rawNodeAt … k false`.
    - `RawNode.Advance.spec` is now `{rawNodeAdv} … {rawNodeAt k false}`. Its sketch, and
      `node.Advance`'s, say how the channel handshake applies the rendezvous.
  - **R3 (`ApiLog.lean`)**:
    - `LogState` has a ghost field `floor`, the published floor, with `Wf: floor ≤ applying`.
    - `compactFloor = max base (max applied floor)`.
    - `raftLog_publish` accepts `i ≤ applying` with `handing = false` and records the floor.
  - **The window.** While the acknowledgements step, the floor is ahead of `applied`. A `MsgHup`
    in that window would scan compacted entries in `hasUnappliedConfChanges` and panic. Go never
    does this, because `node.run` is sequential. The specs now make the window explicit with a new
    exclusive token, `coreIdle r`:
    - `rawNodeAt_core` lends it;
    - `stepPre .outside` takes it, and `stepPost` (now with `r`) gives it back;
    - `hup`, `tickElection` and `tickHeartbeat` take and give it;
    - `appliedTo`'s leader branch takes it (it comes with the apply acknowledgement's `ackOk`);
    - `hasUnappliedConfChanges` takes the premise `floor ≤ applied`;
    - the internal law `coreIdle_floor` gives that premise.

  I did not take the alternative ("pending Advance" node state): it needs the same R3 change and
  still needs the window.
- **P4, `softStateOpt`, `readStatesRO` and `peersPts` cannot be read or built.** Fixed in
  `Api.lean`. All three are now transparent definitions over Goose points-to (as `hsOpt` is):
  - `SoftState.mk` read-only;
  - `ReadState` values with `RequestCtx ↦*□`;
  - `Peer` values with `Context ↦*{dq}`.

  `persistent.spec` still lists the first two, which stay persistent.
- **P5, `raft_init` is missing package variables.** Fixed in `ApiCore.lean`. `raft_init.spec` now
  also gives:
  - `raftLoggerMu`'s lock invariant (`sync.isMutex`; `raftLogger` meets `loggerOk`);
  - `globalRand.mu` (`isMutex`, invariant `True`);
  - `emptyState`, the empty hard state;
  - `stmap`, four names (`GoArray GoString 4`);
  - `errBreak`, a non-nil `errIs`;
  - the `isLocalMsg`/`isResponseMsg` tables (`GoArray Bool 23`, entry `t` equal to
    `isLocalMsgType t` / `isResponseMsgType t`).
- **S1, `ReqBootstrap` asserts more than the specs give.** Fixed differently: I dropped the checks
  of raft's internal fields and of the number of committed entries handed out. No caller reads
  them, and `MaxCommittedSizePerReady` may split the entries.
- **S2, snippet assumptions.** Fixed. `ReqReadyStale` assumes `stepMsg`/`stepIn` of `m`.
  `ReqFields` assumes `msgPts` and a type `≥ 0`.
- **S3, margins.** Fixed:
  - `MemoryStorage.Entries` has a margin on `limitSize`'s sum not wrapping;
  - `statusOwn`'s docstring says its `RaftState` is below 4 (`stmap`), and `Status.MarshalJSON`'s
    margin cites it.
- **S4, ghost commit stepping in item 3.** Fixed in the header of `ApiCore.lean`. Item 3 now says
  the ghost commit steps one index at a time, firing the read updates at each length, and why it
  equals the leader's commit at registration.

## A4 completeness

- **F1, snapshot of a delivered entry before `Advance`.** Fixed.
  - **R1**: a new persistent `storedLb n i`.
    - `stor_createSnapshot` takes `storedLb` instead of `appliedLb`.
    - `readyStor_append` now takes `deliveredLb n γ dl` and its COMM gives `storedLb n dl.length`.
      This is sound because no later `Ready` is handed out while `readyStor` exists.
    - New laws: `storedLb_mono` and `appliedLb_storedLb`. `zero_lbs` includes `storedLb`, and
      `persistent.spec` lists it.
  - **R3**: a new persistent `logStored l i t`.
    - `logStor_append`'s COMM gives it for the batch's entries up to `h.upto`.
    - New laws: `raftLog_storedStable` (at the hand-out, from `freezeStable`) and `logFloor_stored`.
    - `logStor_createSnapshot` takes `logStored`.
  - The realization is in both headers.
  - Snippets: `ReqSnapshotCompact` now derives `storedLb` from `appliedLb`. New `ReqSnapshotMidBatch`
    in `raftnode/storage.go`.
  - `stor_compact` still needs `appliedLb`.
- **F2, the `Ready`'s soft state, read states and `StartNode`'s peers.** Fixed (= P4).
  `ReqStartFresh`'s `Specs` line now names the definitions.
- **F3, `loggerOk` has no introduction.** Fixed in `Api.lean`. `loggerOk` is now a transparent
  bundle, as `isStorage` is: a non-nil interface whose `Debugf`/`Infof`/`Warningf`/`Errorf` (any
  format and arguments) and `Error` (any arguments) return. That covers every method raft calls
  outside panic paths: I grepped `.lake/src/raft`. New snippet `ReqClientLogger` in
  `raftnode/restart.go`, with a `quietLogger`.
- **F4, `MemoryStorage.firstIndex`/`lastIndex` have no spec.** Fixed: new
  `MemoryStorage__firstIndex.lean` and `MemoryStorage__lastIndex.lean`. Each is over the `ents`
  field and `entriesRO sl k es`, with `es ≠ []`, and returns `k+1` or `k+|es|-1`.
- **F5, `appliedLb`'s docstring.** Fixed differently. I kept the clause and made it true:
  `readyStor_install`'s COMM now also gives `appliedLb n s.index`, which R3's `logStor_install`
  already publishes as a floor.

## A5 (R3 parts) and raft-conf-pb's relayed requests

- **F1, `DescribeConfChange` has nothing to be proved from.** Fixed in `DescribeConfChange.lean`:
  it is now stated as assumed at the trust boundary. The reason given: `fmt.Fprintf` into a
  `strings.Builder` has no spec in Perennial or here. `ConfChangesToString` is raftpb's (3h), so I
  did not touch it.
- **F5, `ReqConflictHint` does not close.** Fixed. The re-read now tolerates `ErrCompacted`, and the
  wrong assumption is removed.
- **F6, `ReqMoveBeforeAdvance` does not close.** Fixed:
  - it calls `CreateSnapshot(i, cs, nil)` before `Compact` (`logSnapLb`);
  - it assumes no pending snapshot and the cluster's log matching (`StableOk`);
  - its `Specs` line now names the new publish law.
- **S1, `unstable`'s realization lacks `loggerOk`.** Fixed in `ApiLog.lean`'s header.
- **S2, the last-term check in `ReqReadyCycle`.** Fixed in the snippet's `Assumes` ("applied below
  the in-progress offset at the hand-out"). I did not add it to `Wf`, because I am not certain it is
  true of every state the law must cover.
- **S3, `ReqFollowerAppend` lacks an index bound.** Fixed: `Assumes` now has
  `a.prev.index + len(a.entries) < 2^64`.
- **Completeness F2(b) / raft-conf-pb request (1), `ConfState` fullness.** Fixed.
  - `MemoryStorage.CreateSnapshot.spec` now takes and returns `RaftPb.confStateFull`. Its old
    statement was false when `AutoLeave` is unset.
  - `raft.switchToConfig`, `raft.applyConfChange`, `RawNode.ApplyConfChange` and
    `node.ApplyConfChange` now return `confStateFull`. This relies on raft-conf-pb's
    `ProgressTracker.ConfState`, which now returns it.
- **Completeness F5 / request (2), the async storage messages' posts are false.** Fixed with the
  `msgOut` choice: `newStorageApplyMsg` and `newStorageAppendMsg` now return
  `∃ rs, RaftPb.msgOut p (own 1) mm rs`. I chose this over dropping them as a scope restriction
  because it is true of the code at no cost.
- **Request (3), `RawNode.Bootstrap`'s sketch.** Done: it cites `noMaps_raftpb.spec`,
  `bootEntryData_marshal.spec` and `raft_init`'s `emptyState`. I also removed the stale `node.run`
  user.
- **Request (4).** = F1.
- **Not mine:**
  - completeness F4 (`msgRecv` intro) is raftpb's and 2a's;
  - completeness F1 (`MessageType.String`) is raftpb's.

**Sentinel errors.** raft's errors were already existential (`errs_init`: `errIs` = `globalAddr g
↦□ e`, pairwise distinct, non-nil). `errBreak` is added in the same form in `raft_init`.

## Requests to server-core

- `EtcdServer__snapshot.lean`: `stor_createSnapshot` now takes `storedLb`. Get it from the
  `appliedLb` you hold (`nodeAdvanced`) with `appliedLb_storedLb.spec`. Keep `ep.confState` as
  `confStateFull`: `MemoryStorage.CreateSnapshot.spec` takes it, and `node.ApplyConfChange` now
  returns it.
- `raftNode__start.lean` step 6: `readyStor_append.spec` now also takes the `Ready`'s
  `deliveredLb n γ dl`, which the loop holds from `readyGot`. Its COMM additionally gives
  `storedLb n |dl|`.
- `raftNode__ApplyConfChange.lean`: pass `RaftPb.confStateFull` through, as `node.ApplyConfChange`
  now gives.

## Requests to server-boot

- `ApiBoot.lean` / `wal/Api.lean`: `raftState_crash` now takes a whole state record. Either:
  - the old term and vote with `wcommit ≤ c ≤ D.commit`, or
  - the batch's term and vote with `wcommit ≤ c ≤` the batch's commit.

  `crashedMid`'s two cases already match. Check the `disk_crash` sketch's instantiation.

## New decisions

- **An idle token for the raft struct (`coreIdle`).** `node.Advance` returns before the run
  goroutine steps the acknowledgements. Giving the client `appliedLb` at once means R3 publishes a
  floor ahead of raft's `applied` for that window. A `MsgHup` in the window would panic in Go
  (`hasUnappliedConfChanges`), and `node.run`'s sequencing is what excludes it. The specs now state
  that sequencing as an exclusive token:
  - every step from outside takes it, as do `hup` and the ticks;
  - `RawNode` holds it except between `Advance`'s rendezvous and its steps.

  This changes the shape of R2's `stepPre`/`stepPost` and of `RawNode.Advance.spec`. That triple
  now covers only the steps; a direct `RawNode` caller applies `rawNodeAt_advance` first.
- **`storedLb` as a second, weaker storage bound.** Snapshotting a delivered entry before `Advance`
  (kvdurable, kvreconf) is served by a fact weaker than `appliedLb`. Compaction keeps needing
  `appliedLb`. The old proofs' coverage is kept, and the examples' Go code does not change.
- **`loggerOk` gives the logger no ownership of the arguments**, as the old `isLogger` did. A logger
  that formats them (zap's adapter) rests on its own trust-boundary specs.

## Build

`etc/specs-build.sh --dir Spec/go_etcd_io/raft/v3`: **OK (229 modules)**.
`cd examples && go vet ./specreq/raftnode/...` is clean. The `raftcore` and `raftlog` snippets are
`//go:build ignore`; `gofmt` parses them and finds nothing to change.

## Second pass (coordinator: does the crash law the server cites match?)

The split `raftState_crash` is in the tree: `Spec/go_etcd_io/raft/v3/Api.lean:909`. Its premises
(`:915`, `:917`) are, besides `b.snap = none`, `j ≤ |b.ents|`, `wcommit ≤ hs.commit`,
`hs.commit ≤ (D.crashed b j hs).last` and `confAboveOk`:
- **(old record)** `hs.term = D.term ∧ hs.vote = D.vote ∧ hs.commit ≤ D.commit`, or
- **(batch record)** `∃ h, b.hs = some h ∧ hs.term = h.term ∧ hs.vote = h.vote ∧ hs.commit ≤ h.commit`.

The round-3 statement, which `server-core` describes as current, allowed the old term and vote with
a commit up to the batch's. It no longer exists. Where the citations differ:

- `wal/Api.lean:60-62` (server-boot). It says "R1's `raftState_crash` allows the batch's term and
  vote with a commit from the old `wcommit` up". It should say: "R1's `raftState_crash` allows the
  batch's term and vote with a commit between the old `wcommit` and the batch's commit (its second
  case; the new record's commit is the batch's)". Without the upper bound the citation is wrong.
- `ApiBoot.lean:130-133` (server-boot). It says "a prefix of the batch's entries, the old state
  record, a commit from the synced one up". It should say: "a prefix of the batch's entries with the
  old state record (its term and vote, a commit between `wcommit` and `D.commit`:
  `raftState_crash`'s first case), or all of them with the batch's record (its term and vote, a
  commit between `wcommit` and the batch's: the second case)". The current text drops the
  second case, which `crashedMid` has, and the old record's upper bound `D.commit`.
- `ApiBoot.lean:148` ("`raftState_crash`'s two hard-state cases") and `:578`: these match.
- `raftNode__start.lean:34` (server-core): this matches; it does not restate the cases. If its
  realization of the crash law (the file server-core reports) restates the round-3 disjunction
  (old or batch term and vote, commit up to the batch's), replace it with the two cases above.

## Re-review (`R-A5-raft-log-conf-pb.md`)

- **N1(a)**: fixed. `ReqScanConfChanges` (`raftlog/reads.go`) and `ReqCompactApplied`
  (`raftlog/ready.go`) now assume `floor ≤ applied` (the struct is idle, `coreIdle_floor`). With it,
  `compactFloor` is the applied index or the base, as `scan`'s and `term`'s specs need.
- **N1(b)**: fixed. `ReqCompactApplied` and `ReqMoveBeforeAdvance` now assume their `cs` is full
  (`confStateFull`, `AutoLeave` set), which `MemoryStorage.CreateSnapshot.spec` takes.
- **Second tier, `ReqBootstrapBytes`**: not fixed. The snippet is in `examples/specreq/raftpb/`,
  which belongs to raft-conf-pb. **Request to raft-conf-pb**: add to its `Assumes` a bound on the
  context length large enough for `proto.Marshal`'s size premise. etcd's member JSON is small.
- No code changed, only `Assumes` lines. `gofmt -l specreq/raftlog` finds nothing to change.

### Re-review of A4 (`R-A4-raft-node-core.md`)

- **N1**: fixed in `Api.lean`. `raftState_crash`'s batch-record case now requires
  `j = b.ents.length`: the state record follows the entries in the write. The docstring explains
  why. WAL's `crashedMid` and `disk_crash` use only the all-entries case, so no caller changes.
- **N2**: fixed in `raft__hasUnappliedConfChanges.lean`. The premise is now
  `compactFloor ≤ applied`, which covers both the published floor and the base, so it excludes a
  pending restored snapshot. `hup` has it after `promotable` (no pending snapshot) and
  `coreIdle_floor`.
- **S-a**: fixed. `rawNodeAt_advance`'s realization now names the install's floor
  (`logStor_install`'s `logFloor l s.index s.term`, kept by `readyStor rn none j []`) for a batch
  with a snapshot.
- **S-b**: fixed. `ackOk`'s docstring now says `coreIdle` stays in `rawNodeAdv` and returns at
  `rawNodeAdv_open`'s closing. Only an apply acknowledgement lends it, for `appliedTo`'s auto-leave
  proposal.
- **S-c**: fixed. `ApiLog.lean` exports `logStored_mono` and `logFloor_mono` (downward closed),
  which `storedLb_mono` and `appliedLb_mono` rest on.
- **S-d**: not done here. `notes/perennial-changes.md` is outside my ownership. **Request to the
  coordinator**: add an entry there for the missing `fmt.Fprintf` / `strings.Builder` specs, which
  are why `DescribeConfChange` is assumed.
- Build after these fixes: `etc/specs-build.sh --dir Spec/go_etcd_io/raft/v3` OK (229 modules); `go vet ./specreq/raftnode/...` clean.
- **Recheck NR1** (`RR-raftlog-bbolt.md`): fixed. `ReqCompactApplied` (`raftlog/ready.go`) now assumes `applied >= base` as well as `floor <= applied` (not between a restore's `stableSnapTo` and its `appliedSnap`). The false comment is corrected: `compactFloor` is then the applied index. `gofmt` is clean.
