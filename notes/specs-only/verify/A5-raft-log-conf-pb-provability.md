# A5 (raft log, conf, raftpb): provability

Reviewer: provability kind, verification round (2026-11-09), on `specs-only` at `1aa6fc1337`.
Area: batch **R3** (`ApiLog.lean`, the specs of `log.go`, `log_unstable.go`, `read_only.go`,
`util.go`, `types.go`), batch **R4** (`tracker/`, `quorum/`, `confchange/`), batch **3h**'s raftpb
part (`raftpb/`), and the snippets `examples/specreq/{raftlog,raftconf,raftpb}/`. Callees checked:
`Spec/google_golang_org/protobuf/proto/`, `isStorage` in `Api.lean`, the `MemoryStorage.*` specs,
and Perennial's `fmt`, `strings` and `slices`.

I wrote the findings below before reading the batch, integration and open-question notes. I read
them afterwards only to see which findings were already recorded (marked **known**). None of the
findings is a pending user decision.

## Verdicts

| batch | verdict | why |
|---|---|---|
| R3 (log, read-only queue, util) | **FAIL** | `DescribeConfChange.spec` has nothing to be proved from (F1). Two snippets do not close (F5, F6). |
| R4 (tracker, quorum, confchange) | **FAIL** | The "unexpected conf type" path in `Changer.apply.spec` calls `fmt.Errorf` with an argument Perennial's spec does not admit (F2). Three snippets use `proto.Uint64` (no spec) or read `Learners` (no law) (F7, F8). |
| 3h raftpb | **FAIL** | The mismatch path of `ConfState.Equivalent.spec` (F3) and all of `ConfChangesToString.spec` (F1) cannot be proved. No law ties `bootEntryData` to `proto.Marshal`'s output, which R1's `RawNode.Bootstrap` and `ReqBootstrapBytes` need (F4, known since I3, not fixed). |

Every fix below is small: a trust-boundary spec, one law, or a snippet's `Assumes` or body. The log
invariant, the quorum, tracker and confchange models, and the raftpb ownership design all hold up.

## Counts

- **Function specs: 182 checked, 178 close.** R3: 66 (33 `raftLog`, 13 `unstable`, 5 `readOnly`
  plus `newReadOnly`, `newLogWithSize`, 12 from `util.go`, `pbEntryID`). R4: 31 tracker, 7 quorum,
  22 confchange. 3h: 56.
  - Do not close: `DescribeConfChange`, `Changer.apply` (its error branch), `ConfState.Equivalent`
    (its mismatch branch), `ConfChangesToString`.
  - `Changer.Simple`, `EnterJoint` and `Restore` close given `Changer.apply.spec` as stated. They
    inherit F2 only through it.
- **Laws: 75 checked** (ApiLog 18, tracker 7, quorum 9, confchange 9, raftpb 32). All are plausible
  from their stated realization, and none makes the vocabulary vacuous. One law is missing (F4).
- **Snippets: 50 checked, 41 close, 8 do not, 1 uncertain.**
  - raftlog: 18 snippets, 14 close. Fail: `ReqConflictHint`, `ReqMoveBeforeAdvance`; second tier:
    `ReqReadyCycle`, `ReqFollowerAppend`.
  - raftconf: 18 snippets, 14 close. Fail: `ReqLastVoter`, `ReqJointCycle`, `ReqLearnerFlag`;
    uncertain: `ReqCloneFresh`.
  - raftpb: 14 snippets, 13 close. Fail: `ReqBootstrapBytes`.

## First-tier findings

### F1. `DescribeConfChange.spec` (R3) and `ConfChangesToString.spec` (3h): the Perennial specs their sketches cite do not exist

- **Evidence.**
  - `util.go:247-259` formats with `fmt.Fprintf(&b, ...)` into a `strings.Builder`.
    `raftpb/confchange.go:156-176` uses `buf.WriteByte`, `buf.WriteString`, `fmt.Fprintf` and
    `buf.String()`.
  - Perennial specifies only `fmt.{Errorf,Printf,Sprintf}`
    (`.lake/packages/perennial/Perennial/Spec/fmt/`). Its `strings` translation is the `Builder`
    type only (`Perennial/Code/strings.toml`: `translate = ["Builder", "asciiSpace"]`), with no
    methods. `fmt.Fprintf` is names-only.
  - This repository has no spec of them either (`Spec/fmt/` holds only `Api.lean` and
    `Sscanf.lean`).
  - Yet the sketches say "`fmt`/`strings.Builder` (Perennial's)" (`DescribeConfChange.lean:5`,
    `ConfChangesToString.lean:6-7`).
  - The old tree assumed `DescribeConfChange` outright, as a trust-boundary axiom
    (`specs-ref/Proof/go_etcd_io/raft/v3/DescribeConfChange.lean`).
- **Affects.** R2's `stepLeader` (`raft.go:1358`, the log line for a refused conf change).
  `ConfChangesToString` has no caller with a spec: its `Users` line is stale. `util.go:216` is
  `DescribeEntry`, not `DescribeConfChange`.
- **Fix.** State both as assumed at the trust boundary. Either:
  - add specs of `fmt.Fprintf` into a `*strings.Builder` (any string; the arguments' getters only)
    and of `strings.Builder.{WriteByte,WriteString,String}`, in `Spec/fmt/` and `Spec/strings/`; or
  - mark the two functions' triples as assumed, with the reason (formatting only; the conf change
    is read and given back).

  Fix the `Users` line of `ConfChangesToString`.

### F2. `Changer.apply.spec` (R4): the "unexpected conf type" error cannot be proved from Perennial's `fmt.Errorf`

- **Evidence.**
  - `confchange.go:167` is `fmt.Errorf("unexpected conf type %d", cc.GetType())`. The argument is a
    `raftpb.ConfChangeType`, whose method set has `String` (`Code/go_etcd_io/raft/v3/raftpb.lean:2608`).
  - Perennial's `fmt.Errorf.spec` requires `ArgsWf`: predeclared basic types, or named integers with
    no `String`/`Error`/`Format`/`GoString` (`Perennial/Proof/fmt/Base.lean:342-350, 517-524`).
    `ConfChangeType` is neither, so no spec applies.
  - The old proof needed a local trust-boundary `Spec/fmt/Errorf.lean` (`argsOk`, with
    `ConfChangeType.String`'s spec); see `specs-ref/Proof/.../confchange/Changer__apply.lean:191-194`.
    Neither exists on this branch.
  - The `none` branch of `applyOne` (an unknown type) is in the spec's precondition. The spec
    promises an error there, and `Simple`, `EnterJoint`, `Restore` and R1's `changeV2` all rely on
    it. kvreconf's pre-check passes arbitrary changes.
- **Fix.** Restore a trust-boundary `fmt.Errorf` spec for arguments of named integer types whose
  `String` Go does not call under `%d`. In Go, `handleMethods` calls `String` only for `%v %s %x %X
  %q`. Alternatively, propose a Perennial change that widens `ArgsWf` to that case. Cite it in
  `Changer.apply`'s sketch.

### F3. `ConfState.Equivalent.spec` (3h): its mismatch branch calls `fmt.Errorf` with `*ConfState` arguments

- **Evidence.**
  - `confstate.go:49` is `fmt.Errorf("...%+#v...", cs1v, cs2v, cs, cs2)`: four pointers, not
    `ArgsWf`.
  - The spec states `err = nil ↔ cs1.Equiv cs2` for every input, so its proof must take this path.
    The sketch (`ConfState__Equivalent.lean:16`) says "`fmt.Errorf` (Perennial's `fmt`)", which
    does not cover these arguments.
  - The old spec stated only the `nil` result, under the premise `Perm`.
  - The only raft caller, `assertConfStatesEquivalent`, needs only the `Equiv → nil` direction. The
    snippet `raftpb/ReqEquivalent` needs the mismatch error.
- **Fix.** Either:
  - a trust-boundary `fmt.Errorf` spec for pointer arguments under `%#v`. Go calls only
    `GoString`, which protobuf messages do not have; it reads the struct by reflection and writes
    nothing. This can share F2's boundary file.
  - or weaken the spec to the premise `cs1.Equiv cs2` and drop the mismatch requirement from
    `ReqEquivalent`.

  The first keeps the stronger spec.

### F4. raftpb has no law making `bootEntryData` the bytes `proto.Marshal` gives (3h; known at I3, not fixed)

- **Evidence.**
  - `bootEntryData` is opaque (`raftpb/Model.lean:424`). `bootCC_facts` (`raftpb/Api.lean:456`)
    gives only `Proto.encodes ConfChange.ty c (bootEntryData id ctx)`, and `encodes` is not a
    function from content to bytes.
  - 2a's `Marshal.spec` now gives `noMaps t → bs = marshalOut t c`. But `Proto.noMaps` is opaque
    with no intro law anywhere (`grep -rn noMaps Spec` finds only its uses), so no client can
    discharge it.
  - R1's `RawNode.Bootstrap.spec` takes `BootLog ps boot` with `e.data = bootEntryData p.1 p.2`
    (`Model.lean:416`). Its proof must show that the bytes `proto.Marshal` returned are
    `bootEntryData`, and it cannot.
  - `ReqBootstrapBytes` still says "BLOCKED". The Model header (`raftpb/Model.lean:61-65`) already
    names the intended fix. `integration-I3.md:160-161` lists it as a to-do for the raftpb owner.
- **Fix.** Add the raftpb laws `noMaps_raftpb.spec : Proto.noMaps raftpb.ConfChange.ty` (and the
  other raftpb types, which have no map fields) and
  `bootEntryData_eq.spec : ∀ id ctx c, bootCC id ctx c → bootEntryData id ctx = Proto.marshalOut
  raftpb.ConfChange.ty c`. Then unblock the snippet.

### F5. Snippet `raftlog/ReqConflictHint` does not close (R3)

- **Evidence.**
  - `reads.go:56-57` re-reads `l.term(j)` for every `j` in `(hint, index]` and panics on any error.
  - `raftLog.term.spec` admits `ErrCompacted` for `i < compactFloor` (`raftLog__term.lean:50`),
    and the storage may be compacted concurrently up to the floor.
  - The `Assumes` line ("index >= committed, so no re-read is below the compaction floor") is
    wrong. `findConflictByTerm` walks down past `committed`, so `hint` can be far below
    `compactFloor`.
  - The callers (`raft.go:1519, 1839`) use the hint only as a hint.
- **Fix.** Assume no concurrent compaction below `index`, or allow `ErrCompacted` in the re-read
  (`err != nil && err != ErrCompacted`). The spec is right as it is.

### F6. Snippet `raftlog/ReqMoveBeforeAdvance` does not close (R3)

- **Evidence.**
  1. `ready.go:113`: `st.Compact(i)` goes through `logStor_compact` (`ApiLog.lean:630-634`), which
     needs `logSnapLb l i`: a stored snapshot at `i` or later. The snippet creates none, and its
     `Assumes` do not give one. etcd always calls `CreateSnapshot` before `Compact`, as
     `ReqCompactApplied` does.
  2. If a snapshot is pending, the hand-out holds it (`logPending … true …`), and `st.Append` needs
     `snapLeft = false`. The snippet does not install it and does not assume none.
  3. After a truncating `append(newer...)`, `stableTo`'s `StableOk` (`log' = log`) needs the
     cluster's log matching when `newer` has the acknowledged id. Wf alone does not give it. The
     snippet's `Assumes` ("as ReqReadyCycle") claim Wf suffices.
- **Fix.** Call `CreateSnapshot(i, …)` first (or assume `logSnapLb l i`), assume no pending
  snapshot, and add the log-matching assumption.

### F7. Snippets `raftconf/ReqLastVoter`, `ReqJointCycle`, `ReqLearnerFlag` use `proto.Uint64`, which has no spec (R4)

- **Evidence.** `raftconf/confchange.go:14`:
  `&pb.ConfChangeSingle{..., NodeId: proto.Uint64(id)}`. `proto` is translated names-only
  (`Code/google_golang_org/protobuf/proto.toml`), and `Spec/google_golang_org/protobuf/proto/` has no
  `Uint64`. The raftpb snippets already switched to `new(id)` (`batch-3h.md:194`).
- **Fix.** Use `new(id)` in `single`.

### F8. Snippet `raftconf/ReqLearnerFlag` reads `trk.Learners[id]`, which no law exposes (R4)

- **Evidence.** `voters.go:63`. `configOwn` is opaque, and `configOwn_open.spec` gives only
  `Voters` (`jointConfigOwn`) and `AutoLeave`. Raft itself never reads `Learners` or `LearnersNext`
  directly (`grep` over `.lake/src/raft/*.go`), so the snippet asks for more than the users need.
- **Fix.** Read the learners through `ProgressTracker.LearnerNodes` (or `ConfState()`) in the
  snippet. If a real user needs the maps, extend `configOwn_open` to return
  `majorityOwn cfg.Learners' dq m.learners` and the same for `LearnersNext`.

## Second tier

- **S1 (R3).** `unstable`'s intended realization (`ApiLog.lean:90-91`) does not hold `loggerOk` of
  `u.logger`. `unstable.stableTo` and `truncateAndAppend` call `u.logger.Infof`
  (`log_unstable.go:142, 213, 222`) with only `unstable u us` in hand. `raftLog`'s realization says
  "loggerOk of both loggers", but the `unstable` specs stand alone. Add it to `unstable`'s
  realization.
- **S2 (R3).** The final `l.term(last)` check in snippet `ReqReadyCycle` (`ready.go:55`) needs
  `last.index ≥ compactFloor`, which needs `applied < offsetInProgress` at the hand-out. That holds
  in every reachable state (truncation is above `committed`, `restore` past it, `stableTo` only
  raises `offsetInProgress`), but it is not in `LogState.Wf`. Add it to `Wf` (cheap and true), or
  assume it in the snippet.
- **S3 (R3).** Snippet `ReqFollowerAppend` lacks `a.prev.index + len(a.entries) < 2^64`, a premise
  of `maybeAppend.spec`. `entriesRO`'s `W64 (k+j)` does not give it. Add it to `Assumes`.
- **S4 (R4, uncertain).** `ReqCloneFresh` deletes from `c.Voters[0]` inside `range c.Voters[0]`.
  Whether Perennial's map-range rule lets the body write the map it ranges over is not checked
  here.
- **S5 (3h).** `raftpb/Api.lean:58`'s header still names `mergeDstOk`. It should be
  `Proto.mergeDst` (known, `integration-I3.md:159`).

## Proof plans (summary; every step closes unless named above)

### R3

**The log invariant** (ApiLog's realization): checked against each client-write law and each read.

- `raftLog.term`, `firstIndex`, `slice` and `mustCheckOutOfBounds` answer `ErrCompacted` only below
  `compactFloor`, and their `logCompactedLb` holds.
  - The storage's `off` is at most the largest published floor. Floors are the attach point, a
    `raftLog_publish`ed `i ≤ applied`, or an installed snapshot, which is at most the base.
    `compactFloor = max base applied` is monotone, since `restore` needs `s.index > committed ≥
    base`.
  - The storage snapshot is at least `off`, and a pending snapshot is at least every
    `logCompactedLb` it issued.
- `isStorage.Term`'s `j ≤ σ.last` and `Entries`' `hi ≤ σ.last+1` hold. While a batch is out,
  `stable < h.start`, because `stableTo` needs `handing = false`. So a written batch never shortens
  the storage below `stable`, and with no unstable part and no pending snapshot there is nothing to
  write.
- `logStor_install` refuses no snapshot. Floors are at most `committed`, which is below the pending
  snapshot. No floor exists at a pending snapshot's index before its install, so no
  `createSnapshot` reaches it.
- `logFloor_agree` holds: the attach floor, the install floor and `publish` (`freezeStable`
  prefers `frozen`) agree, and a stale snapshot's index cannot be published after a newer
  `restore`.
- The only loose end: `absorb` of a stale batch after `restore` may set `stored` to misaligned
  entries. It is harmless, since the relation is suspended while the snapshot is unstored and the
  next install's `absorb` resets `stored`.

**Function specs.**

- `newLogWithSize`: `FirstIndex`, then `LastIndex`, through `isStorage` on the `S σ` it holds.
  `LogState.init` satisfies `Wf`.
- `lastIndex`, `firstIndex`, `term`, `matchTerm`, `lastEntryID`, `isUpToDate`: `lastIndex ≥
  compactFloor`. Without a pending snapshot, `lastIndex = end ≥ committed`; with one,
  `lastIndex = base = compactFloor`. `termOf (2^64-1) = none` under `Wf`, so the wrap disjunct of
  `term` is harmless to `findConflictByTerm`.
- `maybeAppend`: `matchTerm` is exact (`prev ≥ committed ≥ compactFloor`). `findConflict` needs
  `k > compactFloor`. The `Panicf` is excluded by the log-matching premise. `append` gets
  `k ≤ end+1` from `lastIndex ≤ end`. `commitTo(min(c, lastnew))` follows.
- `append`, `truncateAndAppend`: the capacity disjunct covers aliasing by `u.entries = ents`. The
  middle case appends to a slice with no spare capacity.
- `slice`: storage first, then unstable. `extend` gets `cap < len+len` from `Entries`'
  `len = cap`, and the unstable part is non-empty in that branch.
- `entries`, `scan`, `nextCommittedEnts`: `maxSize > 0` comes from `Wf`'s unpaused budget. There
  is no `ErrCompacted` above `applying ≥ base`.
- `appliedTo`, `acceptApplying`, `commitTo`, `maybeCommit`: the panics are excluded by the
  premises.
- `stableTo`, `stableSnapTo`: `StableOk` and `SnapAckOk` keep the relation.
- `restore`: `V s` is kept for `snapshot()` and `nextUnstableSnapshot`. `logStorage`'s `V` is
  persistent (`logFresh_attach`'s premise).
- `snapshot`: `proto.Clone`, then a type assertion that cannot fail by `Clone.spec`'s `msgVal`.
  Otherwise `Storage.Snapshot` inside the invariant.
- `unstable.*`: these mirror the code, with `us.Wf` bounding each index. The entries' `Index`
  fields come from `entriesRO`, which `acceptInProgress` needs.
- `readOnly.maybeAdvance`: `c.CommittedIndex(ro)` with `isAckedIndexer` built from
  `readOnly.AckedIndex.spec` (the `P` threaded). `jointIdx_mem` and the premise give `N ≤ position`,
  so both reslices are in bounds.
- `recvAck`: `Uint64` needs 8 bytes (premise). `heartbeatCtx`: `PutUint64` into a fresh 8-byte
  slice.
- Util helpers: `proto.Size` through `entryPts_msgAt`.
- `assertConfStatesEquivalent`: the `nil` path of `Equivalent`.

### R4

- `MajorityConfig.CommittedIndex`: fill the slots from the right, sort (at most `2^62`), and take
  `srt[n-(n/2+1)]`; this is `MajorityIdx`. `VoteResult` matches `majVote`, and `JointConfig`
  combines the halves as Go does.
- The quorum laws hold:
  - Majority intersection holds.
  - Joint intersection across `Adjacent`: counting gives `⌊n/2⌋+1 + ⌊(n+1)/2⌋ = n+1 > n`.
  - `majorityIdx_mem`: the largest `N` with a majority is one of the voters' values.
  - `jointIdx_quorum`, `jointVote_won` and `jointVote_lost` follow from the definitions; the empty
    half is `MajQ ∅ = true`.
- Tracker:
  - `Progress.*` matches the `ProgressV` model field by field.
  - `SentEntries` excludes the snapshot-state panic and `Add`'s full-ring panic by its premises.
  - The `Inflights` ring arithmetic holds below `2^62`. `FreeLE` indexes within the buffer because
    wrapping happens only once `len = size`.
  - `Visit`: sorted ids; the callback triple indexed by the visited prefix.
  - `Committed`: the `matchAckIndexer` contract from `matchAckIndexer.AckedIndex.spec`.
  - `ConfState` gets `new(p.AutoLeave)` and four sorted `Slice`s. `Config.Clone` drops `AutoLeave`,
    and the result is still valid.
- Confchange:
  - Model and code agree step by step under `TrackerOk`.
    - `remove` of an untracked id is a no-op.
    - `makeLearner`'s `pr.IsLearner` is `id ∈ learners`.
    - Re-adding a removed peer gives a fresh `Progress` (`Carried`).
    - `checkInvariants ↔ CfgOk` uses the canonical nil-ness.
    - `nilAwareDelete` sets the map to nil exactly when it becomes empty.
  - Laws `changeV2_valid`, `transitions_valid`, `changeV2_adjacent`, `changeV2_single`,
    `restore_lists` (both the joint and the non-joint orders), `restore_valid` and `simple_valid`
    all check out.
  - `chain` composes `Carried`: a fresh `Progress` with its mark updated is still fresh.
  - The one gap is F2.

### 3h

- Getters: `*_unfold`, read, fold back; the nil conjuncts return the defaults.
- `Ensure*`: both cases, `pbRest_zero` for fresh structs.
- `AsV2`: a fresh change and a fresh single, the context shared read-only.
- `EnterJoint` / `LeaveJoint` match `enterJoint` / `leaveJoint`; the unknown-transition panic is
  excluded by `enterJoint = some`.
- `MarshalConfChange`: `AsV1`/`AsV2` dispatch, `Marshal.spec` (fits:
  `encSize ≤ wireBound < 2^48`, `depth ≤ 1`), then `decodeConfChange` by `encodes_fun`. The `nil`
  case uses `decodeConfChange_empty`.
- `Equivalent`'s equal path: `Clone` ×2, `slices.Sort` ×4 (`lenOk`), explicit `AutoLeave`,
  `Equal`, `confState_ext`. The mismatch path is F3.
- The `wireBound` constants cover the encodings: 10 scalar fields at most 11 bytes each, under 256;
  an entry at most 57 bytes plus its data, under 64; a snapshot's frame under 96.

## Snippet sketches (the ones that close)

- **raftlog/start.** Lend `S σ` to `InitialState` (`raftLog_borrowStarting`), then
  `FirstIndex`/`LastIndex` on it. `committed = applied = σ.off`, `lastIndex = σ.last`.
  `lastEntryID` succeeds: `termOf σ.last` is the base term or the last stored entry's. Write
  `committed` within `[committed, end]` (`raftLog_fields`).
- **raftlog/leader-append.** No snapshot pending, so `lastIndex = end ≥ committed`. `append` at
  `li+1`. `term(li+1)` is the term just appended. `maybeCommit` moves `committed`.
- **raftlog/follower-append.** Closes modulo S3. Rejected: unchanged. Accepted: each entry's
  `matchTerm` is exact above `compactFloor`.
- **raftlog/send-or-snapshot.** `ErrCompacted` from `term` or `entries` gives
  `logCompactedLb next`. So `snapshot()` is at index `≥ next ≥ 1`, which is non-empty.
- **raftlog/prev-term.** `lastIndex ≥ compactFloor`.
- **raftlog/scan-conf-changes.** `I` tracks `next = lo + |done|`. A full range has length
  `hi - lo`.
- **raftlog/vote-up-to-date, heartbeat-commit.** Direct.
- **raftlog/ready-cycle.** Closes modulo S2.
  - `acceptUnstable`, then `logStor_install` and `logStor_append` through `MemoryStorage`'s AUs
    (masks `⊤`), then `raftLog_absorb`.
  - `StableOk` from `Wf`'s in-progress agreement. `SnapAckOk` from `snapStored` set by `absorb`.
- **raftlog/compact-applied.** `logStor_createSnapshot` gives `logSnapLb i`, then
  `logStor_compact`. `term(i)` is not compacted: `i = applied` is not below `compactFloor`.
- **raftlog/restore.** Matched: `commitTo`. Otherwise `restore`, then `lastEntryID` is the
  snapshot's, the snapshot is pending, and no committed entries are handed out.
- **raftlog/read-index-quorum.** `u64Le` gives 8 bytes, and every ack is 1. `JointIdx` is 1 when
  self and the others are a quorum of each half (an empty half is `2^64-1`). `advance` hands out
  the one request (`readReqsRO`), and the queue is then empty.
- **raftlog/util snippets.** Direct from `limitSize`, `voteRespMsgType`, `payload(s)Size` and
  `assertConfStatesEquivalent`.
- **raftconf (quorum).**
  - `joint-committed`: `jointIdx_quorum`.
  - `joint-vote`: `jointVote_won`, `jointVote_lost`.
  - `empty-half`: `MajorityIdx` is functional, and `jointVote s0 ∅ = majVote s0`.
- **raftconf (tracker).**
  - `restored` (`MakeProgressTracker`, then `Restore`, then field writes; votes untouched) is
    reused by the tracker and confchange snippets.
  - `committed-quorum`: voters are tracked, so the `Progress` lookup is not nil.
  - `tally-votes`, `visit-sorted`, `inflights-full`, `progress-flow` (each value computed by the
    model), `progress-copy`: direct.
  - `quorum-active`: `activeIds` against `MajQ` on `{1,2,3}`.
  - `voter-reads`: direct.
- **raftconf (confchange).**
  - `apply-like-raft`: `restore_lists` gives `m`. The Changer method that `LeaveJoint`/`EnterJoint`
    selects is `changeV2`'s dispatch. No error means `changeV2 = some`, the premise R1 needs.
  - `restore-empty`, `restore-roundtrip`: `ConfState`'s sorted lists `Lists m`, then
    `restore_lists`.
- **raftpb.**
  - `getters-nil` and `reply-shares-cell` (`From`'s `□` cell, `pbRest_zero`): direct.
  - `field-write`: own 1, write, then fold back.
  - `msgapp-indexes`: `msgEnts_app`, whose `entryIndexes` are defined from `Index+1`.
  - `clone-message`, `clone-snapshot`: `Clone.spec` with `*_msgAt`; distinct from `own 1`.
  - `wire-roundtrip`: `Unmarshal` into a zero message, then `encodes_fun`.
  - `marshal-decode`, `auto-leave` (`zero_facts` and `decodeConfChange_empty`), `asv2`,
    `enter-leave`, `equivalent` (given F3's fix), `ensure` (both cases): direct.

## Bugs in the Go code

None found. Every panic I examined is excluded by a premise that its callers can meet. The known
ones are already filed: `isMsgInArray`'s negative type (`nonissues/`), and the in-process `MsgApp`
aliasing.
