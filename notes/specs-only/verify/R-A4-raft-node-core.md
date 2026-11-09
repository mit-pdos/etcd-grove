# R-A4 (raft node API R1, raft core R2): re-review after the repairs

Reviewer: fresh and independent, read-only. HEAD `974e05095b`; diffs against `1aa6fc1337`.
Scope: the top level of `Spec/go_etcd_io/raft/v3/` without the log files (`raftLog__*`, `unstable__*`,
`readOnly__*`, util), and the snippets `examples/specreq/{raftnode,raftcore}`.

I wrote my verdict on each original finding before I read `repair-raft-core.md`. I read it afterwards
only to check disagreements. I also read the A5 re-review (`R-A5-…`): its N1(a) confirms that the
`scan` premise needs `applied ≥ base`, which bears on N2 below.

## Verdicts

| batch | verdict | why |
|---|---|---|
| **R1** (node API: `Model`, `Api`, `node`, `RawNode`, `MemoryStorage`, starts, `Ready`) | **FAIL** | N1: `raftState_crash`'s batch-record case at `j = 0` is unsound. The other originals are resolved. |
| **R2** (`ApiCore`, `raft.go`, `Ready` phases, loggers) | **FAIL** | N2: `hasUnappliedConfChanges.spec` is false while a snapshot is pending. The rest closes, apart from the open decisions: the term/index bound (open-questions 5.1, via 2.3), `ConfigOk` (2.1, 2.2) and crash scope (2.8). |

Both failures are one-line fixes. Without them, both batches would be PASS WITH OPEN DECISIONS (2.1, 2.2,
2.8, 5.1).

## Original first-tier findings

| finding | status | evidence at HEAD |
|---|---|---|
| P1 `BatchOk` with snapshot + entries | **Resolved** | `Model.lean:381-382`: `entsFrom ≤ (snap ? s.index : durable.last) + 1`. True of Go: `unstable.restore` sets `offset = s.index+1` (`log_unstable.go`). `maybeAppend` cannot truncate at or below `committed = s.index` (`log.go:109-129`). `st.hs.commit < entsFrom` holds because `restore` requires `s.index > committed`. |
| P2(a) crash law vs `BatchOk` (old term with raised commit) | **Resolved, but the new statement has a different hole: N1** | `Api.lean:909-921`: there are now two whole-record cases, and the mixed case is gone. |
| P2(b) entries above the durable term; durable "≤1 conf above `wcommit`" | **Resolved** | `ApiCore.lean` header item 1 ("After a crash …") and item 4 V2 ("in durable terms …"). The argument is plausible. A node with durable term `T` can win at neither `< T'` nor `T'`, because the `T'` electorate's votes are durable before they were granted. |
| P3 `node.Advance`'s post has no source | **Resolved** (two realization gaps, second tier: S-a, S-b) | `rawNodeAt_advance` (`ApiCore.lean:555`) now gives R1's post at the rendezvous and leaves `rawNodeAdv`. `rawNodeAdv_open` covers the steps, and `RawNode.Advance.spec` is `{rawNodeAdv} … {rawNodeAt k false}`. The `coreIdle` token closes the window. `node.run` (`node.go:441-444`) calls `rn.Advance` in the same select arm, so nothing else steps in between. Perennial's select takes the clause pres conjunctively, so the `advancec` clause's receive update can capture `rawNodeAt` and fire `rawNodeAt_advance` at the handshake. |
| P4 / F2 `softStateOpt`, `readStatesRO`, `peersPts` | **Resolved** | These are transparent definitions now (`Api.lean:169-187`). Field shapes match Go: `SoftState{Lead, RaftState}`, `ReadState{Index, RequestCtx}`, `Peer{ID, Context}`. `readyOwn` (`:220`) uses them. |
| P5 `raft_init` missing globals | **Resolved** | `ApiCore.lean` `raft_init.spec` now gives `raftLoggerMu` (`isMutex`, `raftLogger` meets `loggerOk`), `globalRand.mu`, `emptyState`, `stmap` (4), `errBreak` (non-nil) and the two tables (`GoArray Bool 23`). These match `logger.go:54-58`, `node.go:32`, `raft.go:114`, `raft.go:1011` and `util.go:31-52`. The highest index set is `MsgStorageApplyResp = 22`, and `MsgForgetLeader = 23` is outside both tables, hence `getD false`. |
| F1 snapshot of a delivered entry before `Advance` | **Resolved** (one law's realization is short: S-c) | New `storedLb` (`Api.lean`). `readyStor_append` takes `deliveredLb n γ dl` and its COMM gives `storedLb n |dl|`. `stor_createSnapshot` takes `storedLb`, and `appliedLb_storedLb` relates the two. New snippet `ReqSnapshotMidBatch`. |
| F3 `loggerOk` has no introduction | **Resolved** | `loggerOk` is a transparent bundle covering `Debugf`/`Infof`/`Warningf`/`Errorf`/`Error`. That is exactly the set raft calls outside `Panic*`: I counted Debugf 21, Infof 46, Warningf 8, Errorf 1, Error 2, and no `Debug`/`Info`/`Warning`. `loggerOk_nonnil` follows from `interface.ok`. Snippet `ReqClientLogger`. |

The second-tier originals are resolved as well:
- S1 is resolved differently: the checks were dropped, which is fine.
- S2: the `Assumes` lines were added.
- S3: the margins are now in `MemoryStorage.Entries` and `Status.MarshalJSON`.
- S4: added to header item 3.
- F4: `MemoryStorage.{firstIndex,lastIndex}` were restored. They mirror `storage.go:191-206`, with
  `entriesRO sl k es` where the dummy entry is at `k`.
- F5: `readyStor_install`'s COMM gives `appliedLb n s.index`. This is harmless: the storage's
  compaction point is already `s.index`.

## New first-tier findings

### N1. `raftState_crash`'s batch-record case at `j = 0` keeps the old conflicting suffix under the batch's commit (`Api.lean:909-921`, `Model.lean:321-327`)

- **Principles:** Sound; "A premise stated with a □∀ … checked against the reachable states it does
  not pin down".
- **The gap.** `Durable.crashed D b 0 hs` keeps `D` whole (`if es = [] then D`). The second disjunct
  allows the batch's record (`hs.term = h.term`, `hs.commit ≤ h.commit`) at any `j`, including
  `j = 0`. The only bound is `hs.commit ≤ crashed.last = D.last`.
- **Why `h.commit` can reach past `entsFrom`.** `h.commit` can cover the batch's new entries:
  `handleAppendEntries` → `maybeAppend` → `commitTo(min(m.Commit, lastnewi))` (`log.go:129`,
  `raft.go:1815`).
- **Counterexample.**
  1. Follower: durable `ents = [1:t1, 2:t1]`, `commit = wcommit = 1`, term 1.
  2. The term-2 leader has committed `2:t2` and sends `MsgApp(prev 1, [2:t2], commit 2)`.
  3. The batch is `entsFrom = 2`, `ents = [2:t2]`, `hs = (2, v, 2)`. `BatchOk` holds:
     `1 < 2 ≤ 3`, and `2 ≤ next.last = 2`.
  4. Take `j = 0` with the batch's record. Every premise holds: `1 ≤ 2`, `2 ≤ h.commit`,
     `2 ≤ D.last = 2`, and `confAboveOk` (there are no conf entries).
  5. The law yields `raftState` with `commit 2` over `2:t1`.
  6. `RestartNode` (`StorageHolds` holds) then delivers `2:t1` as committed. With the leader's
     `committedLb [1, 2:t2]`, `committedLb_agree` gives `False`.
- **Not true of any storage.** The docstring says the record is written "whole, after the entries".
  etcd's WAL writes the entries, then the state record, and `ReadAll` stops at a torn record. kvdurable
  writes its whole image at once. The WAL's `Recs.crashedMid` (`wal/Api.lean:168-174`) uses the second
  case only with all entries written. A client that wrote the hard state before the entries would hit
  a real safety violation, so the law must not allow that order.
- **Callers.** Nothing that uses the law changes. `disk_crash` (`ApiBoot.lean:130-148`) instantiates
  the second case at `j = |b.ents|` only. But the law as stated cannot be proved, and a client could use
  it to derive `False`.
- **Fix.** In the second disjunct, add `j = b.ents.length`, which is exactly the "record after the
  entries" of the docstring. A more general alternative is
  `(b.ents = [] ∨ 0 < j ∨ uint.nat hs.commit < b.entsFrom)`.

### N2. `raft.hasUnappliedConfChanges.spec` is false while a snapshot is pending (`raft__hasUnappliedConfChanges.lean:31-36`)

- **Principle:** Sound, which holds for internal specs too.
- **What the precondition admits.** Its only new premise is `⌜o.log.floor ≤ o.log.applied⌝`. It
  admits a pending restored snapshot: after `raftLog.restore` (`log.go:466-470`), `committed = s.index`
  while `applied` stays below it, and `floor` is unchanged.
- **Why Go panics there.**
  1. Go scans from `applied+1` (`raft.go:1020-1027`).
  2. `firstIndex()` is `s.index+1` (the unstable snapshot).
  3. So `slice` → `mustCheckOutOfBounds` returns `ErrCompacted` (`log.go:551-557`).
  4. `hasUnappliedConfChanges` then calls `Panicf` (`raft.go:1035-1036`).
- **The proof plan does not close either.** R3's `raftLog.scan.spec` requires
  `compactFloor < lo` with `compactFloor = max base (max applied floor)` (`ApiLog.lean:285`).
  `base = s.index > applied` here. R-A5's N1(a) notes that its R3 snippet assumes `applied ≥ base`
  for this reason.
- **The only caller is unaffected.** `hup` reaches the call only after `promotable()`, which is false
  while a snapshot is pending (`raft.go:1947-1950`; `CampaignGuard` has `us.snap = none`).
- **Fix.** Take `⌜o.log.compactFloor ≤ o.log.applied⌝`, or `⌜o.log.us.snap = none⌝` plus an
  invariant fact `base ≤ applied` when no snapshot is pending. For example, extend `coreIdle_floor` to
  give `o.log.us.snap = none → o.log.base ≤ o.log.applied`. `hup` supplies either one.

## Second-tier findings (new)

- **S-a. `rawNodeAt_advance`'s realization does not cover a snapshot batch** (`ApiCore.lean:538-553`).
  - It says the delivered log is published by `raftLog_publish` at `i ≤ applying`.
  - For a snapshot batch, `|delivered| = s.index`, but `applying` is still the old value:
    `restore` does not move it, and `acceptReady` moves it only when there are committed entries
    (`rawnode.go:431-435`). So `raftLog_publish`'s premise fails.
  - The fact exists: `logStor_install`'s COMM gives `logFloor l s.index s.term`.
  - Fix: state that `readyStor rn none j []` keeps that persistent floor for raft's side, or let
    `raftLog_publish` accept `i = base` when `snapStored`.
- **S-b. Where `coreIdle` sits outside the apply acknowledgement.**
  - `ackOk`'s docstring places `coreIdle` only in the apply acknowledgement.
  - A batch with no committed entries has no apply ack. A snapshot batch also has none: its
    acknowledgement is `appliedSnap` in the append response.
  - In those cases the token must be kept in `rawNodeAdv` and returned by `rawNodeAdv_open`'s closing.
  - The `appliedTo` leader branch is reached only through the apply ack, and `appliedSnap` runs at a
    non-leader, so the steps close.
  - Fix: one sentence in the docstring. These are package-internal predicates, so no law is needed:
    `ackDone`'s producer is internal in the same way.
- **S-c. `storedLb_mono`'s stated realization (`i = 0 ∨ logStored l i t`) needs a downward law of R3's
  `logStored`, which `ApiLog.lean` does not export** (`Api.lean:878`).
  - `appliedLb_mono` has the same pattern with `logFloor`.
  - Semantically the law is true. Below the stored snapshot's index, `CreateSnapshot` answers
    `ErrSnapOutOfDate`, so the term is not needed there.
  - `ReqSnapshotMidBatch` uses it, at `e.index < |dl|`.
  - Fix: R3 exports `logStored l i t ⊢ ∀ j ≤ i, …` (stored at the committed term, or at or below the
    stored snapshot). Alternatively, state the realization of `storedLb` as downward closed.
- **S-d. `DescribeConfChange` is now assumed at the trust boundary**, because there is no
  `fmt.Fprintf`/`strings.Builder` spec. The claim is true of `util.go:247-259`. Record it with the
  Perennial gaps (`notes/perennial-changes.md`) so that it is not forgotten.

## Regressions: every changed spec file in the area (27)

Each was checked against the current callee specs and the Go code.

- **`Model`**: `BatchOk` (P1) closes, and `Durable.next` already cuts at the snapshot.
- **`Api`**:
  - the definitions (P4) and `loggerOk` (F3) close;
  - `storedLb`, `readyStor_install`/`_append`, `stor_createSnapshot` and `appliedLb_storedLb` are
    plausible from R3's `logStor_install`/`logStor_append`, `raftLog_storedStable` and
    `logFloor_stored`, apart from S-c;
  - `raftState_crash` is N1.
- **`ApiCore`**: the header items 1, 3 and 4, `rawNodeAt_core` (it lends `coreIdle`),
  `rawNodeAt_advance`/`rawNodeAdv_open` (S-a, S-b), `stepPre`/`stepPost`, `coreIdle_floor`
  (consistent: `logStor_install`'s floor does not move `ls.floor`, and the base covers it) and
  `raft_init` all close.
- **The steps**: `raft.Step`, `stepLeader`/`stepFollower`/`stepCandidate`, `hup`, `tickElection` and
  `tickHeartbeat` close.
  - Every outside source holds `coreIdle`: `rawNodeAt_core`, the ticks, and `appliedTo`'s
    auto-leave proposal (`raft.go:742-758`, a `stepIn` local proposal with `isEmptyV2`).
  - The acknowledgements never reach `hup` (`ackOk_type`).
- **`appliedTo`**: closes. **`hasUnappliedConfChanges`**: N2.
- **`RawNode.Advance`, `node.Advance`**: close given P3's plan.
- **Unchanged in substance, close**: `RawNode.Bootstrap` (it cites `bootEntryData_marshal`,
  `noMaps_raftpb` and `emptyState`, all present), `RawNode`/`node`/`raft.applyConfChange` and
  `switchToConfig` (now `confStateFull`, which needs R4/A5's `ProgressTracker.ConfState`),
  `MemoryStorage.{CreateSnapshot,Entries,firstIndex,lastIndex}`, `Status.MarshalJSON`,
  `newStorage{Append,Apply}Msg` (now `msgOut`: unreachable under `ConfigOk`, and the post is true) and
  `DescribeConfChange` (S-d).

I found no way to prove `False` and no panicking program proved safe, apart from N1 and N2.

## Snippets

Both packages are clean: `go vet ./specreq/raftnode/` passes and `gofmt -l` prints nothing.

- `raftnode/restart.go`:
  - `ReqStartFresh` closes: `peersPts` is built from the caller's slice, and the nil logger comes
    from `raft_init`'s lock invariant through `getLogger`.
  - **New `ReqClientLogger`** closes. `quietLogger`'s empty `Debugf`/…/`Error` bodies give
    `loggerOk`'s two `□` WPs, which `SetLogger` and `StartNode`'s `cv.Logger'` disjunct take.
- `raftnode/storage.go`:
  - `ReqSnapshotCompact` closes: `appliedLb` → `appliedLb_storedLb` → `stor_createSnapshot`, then
    `stor_compact`.
  - **New `ReqSnapshotMidBatch`** closes given S-c. The steps: `ms.Append` fires `readyStor_append`
    (with `deliveredLb` from `readyGot`), which gives `storedLb |dl|`; `storedLb_mono` brings it to
    `e.index`; `snap_make` and `stor_createSnapshot` follow. Inside `MemoryStorage.CreateSnapshot`'s
    update, `i < off` falls into the `i ≤ snap.index` disjunct. The goroutine and `done` hand-off are
    trivial.
  - It covers the completeness report's U12 (kvdurable `kv.go:504-508` → `:590`, kvreconf
    `:402-406` → `:480`).
- `raftnode/readyloop.go` `ReqReadyLoop`: closes now. P1 and P3 are fixed, `rd.SoftState`/
  `rd.RaftState` read through `softStateOpt`, and `readyStor_append`'s new `deliveredLb` comes from
  `nodeDriver_delivered`.
- `raftcore`:
  - `ReqReadyAdvance` closes: `rawNodeAt_advance`, then `rawNodeAdv_open`.
  - `ReqReadyStale` and `ReqFields` close with their completed `Assumes`.
  - `ReqBootstrap` closes now that it no longer reads raft's internal fields.
  - `ReqLogger` closes from `raft_init`'s `raftLoggerMu` invariant.
- The other REQs are unchanged and still close (`ReqTick` under 5.1).

User patterns from the completeness report: U1, U5, U12 and U24, which failed before, are now covered
by `ReqStartFresh`, `ReqReadyLoop`, `ReqSnapshotMidBatch` and `ReqClientLogger`. N1 does not affect any
user: they all instantiate the safe case.

## Counts

- **Original first-tier findings:** 8 (P1-P5, F1-F3).
  - 8 are resolved. P2(a) is resolved as found, but its replacement has N1.
- **New findings:** 2 first-tier (N1, N2), 4 second-tier (S-a to S-d).
- **Spec files re-checked:** 27 changed in the area. 25 close (two of them need the S-a/S-b wording);
  2 do not (`raftState_crash` in `Api.lean`, and `hasUnappliedConfChanges`).
- **Snippets re-checked:** 6 changed or new REQs, plus `ReqReadyLoop`, `ReqLogger` and
  `ReqStartFresh`, which failed before. All close (`ReqSnapshotMidBatch` given S-c).

## Ranked by need of revision

1. `Api.lean` `raftState_crash`: N1, a soundness hole in raft's crash law.
2. `raft__hasUnappliedConfChanges.lean`: N2, with `coreIdle_floor` if that route is chosen.
3. `ApiCore.lean` `rawNodeAt_advance` and `ackOk` docstrings: S-a, S-b.
4. `Api.lean` `storedLb_mono` / `appliedLb_mono`, together with R3's `ApiLog.lean`: S-c.

## Go code

I found no new bug in the Go code. N1 describes what would be unsafe for a storage that writes the
hard state before the entries. No real client does this, so it is a spec issue and goes in `notes/`,
not `issues/`. `issues/raft-commit-lost-with-entries-kept.md` stays consistent with the specs:
`confAboveOk` is still the premise, and open-questions 2.8 is still open.
