# Batch R3: raft's log (report)

Author agent, 2026-11-09. Everything builds: `etc/specs-build.sh --dir Spec/go_etcd_io/raft/v3`
(131 modules with R1's; R3's are `ApiLog` and 63 spec files). Snippets: `examples/specreq/raftlog/`
(`//go:build ignore`, package `raft`), gofmt-clean, and `go vet` clean when copied into a copy of the
pinned raft module (`565c2bd`) without the build tag.

## Files

- `Spec/go_etcd_io/raft/v3/ApiLog.lean`: the vocabulary (namespace `Raft`, importing R1's `Api`).
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

1. **A suspected raft bug (code reading, not yet confirmed by a test).** With synchronous storage
   writes (etcd), a follower whose `Ready` hands out snapshot `s1` and entries after it can, before
   `Advance`, receive a newer snapshot `s2` (`restore`) and a `MsgApp` after `s2` re-sending entries
   up to the last handed-out index with the same terms. The `Advance` acknowledgement then matches
   (`unstable.stableTo` checks only the index and term, not that the storage holds them after `s2`)
   and marks entries `(s2, id]` stable; the next `Ready` hands out `s2` and the entries after `id`,
   and the storage's `Append` after `ApplySnapshot(s2)` finds a gap (`MemoryStorage.Append` panics
   "missing log entry"). The spec does not hide it: `raftLog.stableTo.spec`'s `StableOk` is false
   there, so R2 cannot step that acknowledgement without a premise. Worth a test in `issues/` (not
   written: outside this batch's paths).
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
