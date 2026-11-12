# Batch R3: raft's log (report)

Author agent, 2026-11-09. Everything builds: `etc/specs-build.sh --dir SpecPlan/Spec/go_etcd_io/raft/v3`
(131 modules with R1's; R3's are `ApiLog` and 63 spec files). Snippets: `examples/specreq/raftlog/`
(`//go:build ignore`, package `raft`), gofmt-clean, and `go vet` clean when copied into a copy of the
pinned raft module (`565c2bd`) without the build tag.

## Files

- `SpecPlan/Spec/go_etcd_io/raft/v3/ApiLog.lean`: the vocabulary (namespace `Raft`, importing R1's `Api`).
- `newLogWithSize`, `raftLog__{maybeAppend, append, findConflict, findConflictByTerm,
  nextUnstableEnts, hasNextUnstableEnts, hasNextOrInProgressUnstableEnts, nextCommittedEnts,
  hasNextCommittedEnts, maxAppliableIndex, nextUnstableSnapshot, hasNextUnstableSnapshot,
  hasNextOrInProgressSnapshot, snapshot, firstIndex, lastIndex, commitTo, appliedTo,
  acceptApplying, stableTo, stableSnapTo, acceptUnstable, lastEntryID, term, entries, isUpToDate,
  matchTerm, maybeCommit, restore, scan, slice, mustCheckOutOfBounds, zeroTermOnOutOfBounds}`
  (35, `log.go`);
- `unstable__{maybeFirstIndex, maybeLastIndex, maybeTerm, nextEntries, nextSnapshot,
  acceptInProgress, stableTo, shrinkEntriesArray, stableSnapTo, restore, truncateAndAppend, slice,
  mustCheckOutOfBounds}` (13, `log_unstable.go`; mirror the code);
- `newReadOnly`, `readOnly__{addRequest, recvAck, AckedIndex, maybeAdvance, heartbeatCtx}` (6,
  `read_only.go`);
- `isMsgInArray`, `voteRespMsgType`, `entsSize`, `limitSize`, `payloadSize`, `payloadsSize`,
  `assertConfStatesEquivalent`, `extend`, `DescribeConfChange` (`util.go`), `pbEntryID`
  (`types.go`).
- Snippets `examples/specreq/raftlog/`: `append.go` (start, leader append and commit, follower
  `maybeAppend` and its hint), `reads.go` (send entries or a snapshot, conflict hint, last/prev
  term, the conf-change scan), `ready.go` (the Ready cycle: hand-out, install, append, acknowledge,
  apply; compaction at an applied index), `snapshot.go` (restore), `readindex.go` (the read-index
  quorum), `util.go` (`limitSize`, vote response types, payload sizes, conf-state assertion).
- Requests: `req/go_etcd_io_raft_v3.md` (`## from R3`: R1's `isStorage.Entries` capacity, the
  intended mapping of R1's storage predicates), `req/go_etcd_io_raft_v3_raftpb.md` (`entryRO`,
  getters, `ConfState.Equivalent`, `Clone`), `req/go_etcd_io_raft_v3_quorum.md` (new: R4's
  `JointConfig` ownership and `CommittedIndex` over an `AckedIndexer` contract),
  `req/google_golang_org_protobuf_proto.md` (new: `proto.Size` of an entry).

## Exported vocabulary (`ApiLog.lean`, namespace `Perennial.EtcdGrove.Raft`)

Pure, transparent:
- `UnstableState` (the `unstable` struct: pending snapshot, entries, `offset`,
  `snapInProgress`, `offsetInProgress`) with Go-faithful `maybeFirstIndex`, `maybeLastIndex`,
  `maybeTerm`, `nextEntries`, `nextSnapshot`, `acceptInProgress`, `stableTo`, `stableSnapTo`,
  `restore`, `truncateAndAppend`, `Wf`.
- `LogState` (`us`, `committed`, `applying`, `applied`, the applying budget, and the ghost fields
  `base`/`baseTerm`, `stored` (raft's knowledge of the storage's entries), `snapStored`,
  `handing`), with `stable`, `end`, `lastIndex` (Go's), `firstIdx`, `compactFloor` (the index the
  storage may be compacted to: `max base applied`), `log`, `range`, `termOf` (Go's `term` absent a
  concurrent compaction), `maxAppliable`, `init`, `truncateAppend`, `conflict`, `appendFrom`,
  `stableTo`, `stableSnapTo`, `restore`, `handout`, `acceptUnstable`, `absorb`, `appliedTo`,
  `acceptApplying`; `Wf`; the acknowledgement premises `StableOk`, `SnapAckOk`.
- `Handout` (a batch handed out: snapshot, first index, entries).
- `ReadOnlyState` (`option`, `acks`, `pending` (request pointer, message pointer, index),
  `confirmed`) with `position`, `recvAck`, `ackOf`, `advance`; `MajorityIdx`, `JointIdx` (quorum
  indices; R4's if it defines them).
- `ConfState.Equiv`.

Resources, opaque:
- `raftLog l ls` (excl): the log and its storage (starting mode: owns `S σ`; attached: through its
  invariant).
- `logStarting l S σ` (excl): not yet attached, storage at `σ`.
- `logStorage l S V N` (pers): attached storage `S`, snapshot validity `V`, invariant namespace `N`.
- `logPending l h snapLeft entsLeft` (excl): a handed-out batch's writes left.
- `logFloor l i t` (pers): the storage may be compacted through `i`; its term at `i` is `t`.
- `logSnapLb l j` (pers): the storage's snapshot is at `j` or later.
- `logCompactedLb l j` (pers): an index below `j` was found compacted; the snapshot the log sends is
  at `j` or later.
- `unstable u us` (excl), `readOnly ro rs` (excl); `readReqsRO sl rqs` (transparent: confirmed
  requests, read-only).
- Provisional: `entryRO p k e` (raftpb's, 3h), `jointConfigOwn c dq s0 s1` (quorum's, R4).

Laws (obligations): `logPersistent` (the persistent ones), `logLbs_mono`, `raftLog_wf`,
`raftLog_fields` (`committed`/`applied`/`maxApplyingEntsSize` readable, `committed` raisable within
`[committed, end]`; the `storage` field `↦□`), `raftLog_storageLastIndex` (`Bootstrap`'s
`storage.LastIndex()`), `raftLog_borrowStarting` (lend `S σ` for `InitialState`),
`logFresh_attach` (allocate the invariant; gives `logStorage`, `logSnapLb`, `logFloor` at the
compaction point), `raftLog_absorb` (fold a written batch into `stored`), `raftLog_publish` (an
applied, stable index becomes a floor); the client's writes `logStor_install`, `logStor_append`,
`logPending_noEnts`, `logStor_compact`, `logStor_createSnapshot`, `logStor_read`,
`logStor_setHardState` (atomic updates at any outer mask `⊇ ↑N`); `readOnly_option`.

## Main changes from the old specs

- **One log predicate.** `raftLog l ls` over a Go-shaped `LogState` replaces `ownRaftLog`,
  `ownRaftLogW` (the acknowledgement windows) and their 25-odd fields (`fl`, `fr`, `dt`, `ksn`,
  `sg`, `lent`, `sapp`, `aps`, `sat`, `sip`, `unpersisted`, `pend`, `sn`, ...). The windows are
  ordinary states: the model computes what Go computes (`lastIndex` is the snapshot's index right
  after `stableTo` with a snapshot pending, as in Go), and only the functions that need a settled
  log take a premise (`nextCommittedEnts`: `base ≤ applying` outside `appliedSnap`).
- **The storage**: through R1's `isStorage` (was `StorageModel`'s range ownership `storLog`/
  `storEnd`/`storCompacted` with `StorNames`); its contents live in the log's invariant once
  attached, and the client writes through the log's laws, which state exactly what raft guarantees at
  each write. The storage-side state raft relies on is three persistent facts (`logFloor`,
  `logSnapLb`, `logCompactedLb`) and one token (`logPending`), in place of the frozen-prefix,
  certified-term and sendable-snapshot ghost maps.
- **Snapshot validity** is the client's `V` (raft's core passes `snapValid γ`), checked at
  `restore`, `logStor_createSnapshot` and the attach, returned by `snapshot()`; non-emptiness of the
  sent snapshot follows from `logCompactedLb` (returned with every `ErrCompacted`).
- **Concurrent compaction** is in the specs: `term`, `slice`, `entries`, `matchTerm`,
  `findConflictByTerm` may answer `ErrCompacted` below `compactFloor` (was: no compaction below the
  published floor `fl` could be observed, stated over `fl`).
- **Starting** is explicit (`logStarting`, `raftLog_borrowStarting`, `logFresh_attach`): the old
  `newLogWithSize` returned the storage's resource `R` and the struct; `newRaft`'s `InitialState`
  needs `S σ` itself (R1's non-atomic contract).
- **Relaxed**: `extend`'s in-place case (was: only the allocating case); `acceptApplying`,
  `appliedTo`, `stableTo`, `stableSnapTo` on the one predicate. **Added premises** (each the
  code's): `newLogWithSize`'s `σ.off ≤ σ.snap.index` (R1's `StorageHolds`), `restore`'s
  `s.index + 1 < 2^64`, the `2^63` range bound on `slice`/`entries`/`nextCommittedEnts`/`scan` and
  `extend`'s `len + len < 2^63` (below).

## Left out

- `newLog` (no caller), `raftLog.String` (formatting, called by the logger), `raftLog.allEntries`
  (no caller); `types.go`'s `logSlice.{lastIndex, lastEntryID, valid}` (no caller in raft's code);
  `Describe{HardState, SoftState, ConfState, Snapshot, Ready, Message, Entry, Entries}`,
  `describeMessageWithIndent`, `describeTarget`, `StateType.MarshalJSON` (debug formatting, no
  caller on a verified path, no old spec). `isHardStateEqual` is R1's (`node.go`).
- `logSliceFromMsgApp`, `releasePendingReadIndexMessages` (old specs exist): `raft.go`, R2's.

## Open questions for the user

1. **The suspected `stableTo` gap (round 0's question 1): not a bug with honest peers.** The
   scenario (a `Ready` hands out `s1` and entries through `id`; before `Advance` a newer `s2` is
   restored and a `MsgApp` re-sends `(s2, id]` at the same terms, so the acknowledgement matches and
   the next `Append` after `ApplySnapshot(s2)` finds a gap) needs `restore(s2)`, which runs only when
   `matchTerm(s2.index, s2.term)` fails (raft.go:1927-1934, else it fast-forwards). If a leader then
   re-sends the handed-out `(id, t)`, log matching says the handed-out log agreed with it through
   `id`, so it held `(s2.index, s2.term)` and `matchTerm` succeeded: no restore. A Go reproduction
   (the coordinator's scratch test `snapgap_test.go`) triggers the panic only with a forged
   message. So no `issues/` entry; `StableOk` stays the premise, and its docstring says R2
   discharges it from log matching.
2. **The `2^63` bound on read ranges** (`slice`, `entries`, `nextCommittedEnts`, `scan`): `extend`
   computes `len(dst) + len(vals)` as an `int`, which Perennial's slices (no memory bound) do not
   keep below `2^63`. The premise is local, but R2 must discharge it at `maybeSendAppend` and
   `hasUnappliedConfChanges`, where the range is `lastIndex + 1 - next`: R2 has no bound on the log's
   length (the old notes: a carried bound below `2^63` makes `appendEntry` unprovable). Options: a
   Perennial-level fact that live slices total below `2^63` elements, or a filed scope restriction.
3. **Index wrap premises**: `append`'s `k + |es| < 2^64`, `restore`'s `s.index + 1 < 2^64`,
   `maybeAppend`'s `prev + |es| < 2^64`: the code wraps there; R2 needs them from its messages'
   facts.
4. **`recvAck`'s context**: a non-empty heartbeat-response context shorter than 8 bytes panics the
   leader (`binary.LittleEndian.Uint64`). The premise holds for contexts raft produced (peers echo
   them); a malformed peer message is outside the model (a `nonissues/` entry candidate).

## For R2 (what the log's specs ask of raft's core)

- `StableOk`/`SnapAckOk` at `MsgStorageAppendResp` (from what R2 knows of `ls.stored`: absorbed
  batches, each the log's entries at its hand-out, and the cluster's log matching);
  `raftLog_absorb` of the written batch before stepping the acknowledgement.
- `maybeAppend`'s log-matching premise (past a matching `prev`, the leader's entries agree with
  `committed`'s prefix); `append` above `committed`.
- `restore` only past `committed` (raft.go checks), with `V s` (`snapValid`, from `msgSent`).
- The attach (`logFresh_attach`) after `loadState` (`σ.snap.index ≤ committed`).
- `nextCommittedEnts`: `base ≤ applying` outside `appliedSnap`'s window (`appliedTo` right after
  `stableSnapTo`).
- `maybeAdvance`: voters non-empty, every voter's acknowledgement at most the queue's position
  (contexts the queue produced, within one term).

## Round 1 repairs

Reviews: `reviews/R3-provability-1.md`, `reviews/R3-completeness-1.md`. Rebuilt
(`etc/specs-build.sh --dir SpecPlan/Spec/go_etcd_io/raft/v3`: OK), snippets gofmt-clean and `go vet` clean in
a copy of the pinned raft module.

- **Publishing the applied floor (both F1).** `LogState` has a ghost `frozen : Nat → Option w64`
  (the storage holds a committed entry of that term there): `absorb` freezes each written entry
  that was committed at the hand-out (`Handout.upto`, new) or is committed now and is the log's, and
  the installed snapshot's index; `restore` keeps it and freezes the stored committed part
  (`freezeStable`); nothing resets it. `raftLog_publish` takes `i ≤ applied` and `freezeStable i =
  some t` (frozen, or stable with nothing pending unstored). So an applied index is a floor after
  a truncation or a restore between `Ready` and `Advance`. The realization's "floor ≤ stable" became
  "floor ≤ `σ.last` and ≤ `committed`" (a floor above `stable` is harmless: raft reads the unstable
  part first). Snippet `ReqMoveBeforeAdvance`.
- **`StableOk`/`SnapAckOk` take `handing = false`** (provability F2), and so does
  `raftLog_storageLastIndex`. `Wf` now carries the in-progress agreement (S1: with no batch out,
  `stored` is the log through `offsetInProgress - 1`), so R2 needs only log matching for a matching
  acknowledgement. `absorb` drops the entries of a batch handed out before a `restore` (S2).
- **Slice capacity** (provability F3): `unstable.truncateAndAppend`, `raftLog.append`,
  `raftLog.maybeAppend` take `⌜len = cap⌝ ∨ ownSliceCap` of the appended slice.
- **`isMsgInArray`** takes `0 ≤ sint.Z t` (provability F4); `nonissues/raft-ismsginarray-negative-type-panic.md`
  written, `nonissues/INDEX.md` regenerated (R1's `IsLocalMsg`/`IsResponseMsg` need the same premise).
- **R1's storage laws** (provability F5/F6, completeness F5): `logStor_read` takes `logSnapLb l j`,
  gives `j ≤ σ.snap.index`, commits `logSnapLb l σ.snap.index`; `logFloor_agree` added;
  `logStor_install` commits a floor at the snapshot. `Entries`' capacity is R1's to add (requested).
- **`maybeAppend`'s indexed entries** (completeness F2): the pre is the weakest the code needs
  (`entriesRO` at `prev + 1` with no spare capacity); the sources are requested from R1 (`Msg`'s
  entry indices, `msgSent`), 3h (`msgPts` exposing the slice) and R2 (`logSliceFromMsgApp`):
  `req/go_etcd_io_raft_v3.md`, "from R3, round 1", item 5.
- **The `2^63`/`2^64` premises** (completeness F3, provability S3): kept local; requested R2's index
  bound as `lastIndex < 2^63` (item 4), which discharges all of them; `nextCommittedEnts`' bound is
  needed only when it slices (not paused, no snapshot pending).
- **The suspected bug** (completeness F4): refuted (open question 1 above), no entry.
- Second tier: `raftLog_fields`' wand ends in `==∗` (S4); `nextUnstableSnapshot` takes `logStorage`
  and returns `V s` (S6); the voter-size bound of `maybeAdvance` requested from R4
  (`req/go_etcd_io_raft_v3_quorum.md`). One batch in flight (`acceptUnstable`'s `handing = false`)
  is the cost of `AsyncStorageWrites` off: async writes would need a queue of hand-outs in
  `LogState` and every acknowledgement spec restated.
- **Snippets** (F7, S5): `ReqReadyCycle` checks the term after `stableSnapTo` and states its
  absorb discipline; `ReqCompactApplied` checks the applied index itself, with no other compaction;
  `ReqConflictHint` assumes `index ≥ committed`; `ReqLimitSize` no longer compares pointers;
  `ReqPrevTerm` guards `2^64 - 2`; `ReqReadIndexQuorum` assumes a quorum of each half acknowledged
  and the voter bound; `ReqStart`, `ReqLeaderAppend`, `ReqFollowerAppend` state their missing
  assumptions; new `ReqVoteUpToDate`, `ReqHeartbeatCommit`, `ReqMoveBeforeAdvance`.
- Not changed: the uncertain `assertConfStatesEquivalent` vs `proto.Equal` on unknown fields (3h's
  `confStatePts` should exclude them), and `restore`'s `Infof("%s", l)` (the logger's `String` call
  on the struct the caller owns: `loggerOk`'s owner).
