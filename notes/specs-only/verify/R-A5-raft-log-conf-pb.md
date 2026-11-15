# R-A5: re-review of the raft log, tracker/quorum/confchange and raftpb (2026-11-09)

Reviewer: independent re-review after the repairs. `specs-only` at `974e05095b`, against
`1aa6fc1337`. Area:
- R3: `ApiLog.lean`, plus the specs of `log.go`, `log_unstable.go`, `read_only.go` and `util.go`;
- R4: `tracker/`, `quorum/`, `confchange/`;
- 3h, raft part: `raftpb/`;
- snippets: `examples/specreq/{raftlog,raftconf,raftpb}`.

Also checked, as callees: the norm-based laws against 2a's restated `proto` specs (`Api`, `Clone`,
`Equal`, `Unmarshal`, `Marshal`), and protobuf-go v1.36.12's `internal/impl`.

I wrote the verdicts below before reading `repair-raft-conf-pb.md`. Afterwards I read it and
`open-questions.md` (C32 to C37) only to name the open decisions.

`etc/lean-check.py -a` passes on these files:
- `raftpb/{Api,FmtErrorf,MessageType__String,ConfState__Equivalent}`;
- `ApiLog`;
- `tracker/ProgressTracker__ConfState`.

The commit reports that the full build passes.

## Verdicts

| batch | verdict | why |
|---|---|---|
| R3 (log, unstable, readOnly, util) | **FAIL** (assumptions only) | Every original finding is resolved, and the specs close. Two raftlog snippets no longer close after other groups' changes: R2's `floor` in `compactFloor`, and R1's `confStateFull` premise on `CreateSnapshot`. Each needs one line in its `Assumes` (N1). |
| R4 (tracker, quorum, confchange) | **PASS WITH OPEN DECISIONS** | C35: `Changer.apply`'s error path rests on raftpb's local assumed `fmtErrorf.spec`. |
| 3h raftpb | **PASS WITH OPEN DECISIONS** | C35 (`fmtErrorf`), C36 (`msgRecv_intro` from `mergeDst`), C37 (`msgOut`). |

## Original first-tier findings

P = `A5-…-provability.md`, C = `A5-…-completeness.md`.

| # | finding | status | evidence at `HEAD` |
|---|---|---|---|
| P-F1 | `DescribeConfChange` and `ConfChangesToString` cite Perennial specs that do not exist | **Resolved.** | Both are stated as assumed, with reasons that are true of `util.go:247-259` and `raftpb/confchange.go:156` (`DescribeConfChange.lean:5-9`, `ConfChangesToString.lean:1-25`). The `Users` line is corrected: `util.go:216` is `DescribeEntry`, checked. |
| P-F2 | `Changer.apply`: `fmt.Errorf("%d", ConfChangeType)` is outside `ArgsWf` | **Resolved; open decision C35.** | `raftpb/FmtErrorf.lean` covers it with `FmtArg.enum`. The translation (`Code/.../confchange.lean:705-708`) passes `Convert ConfChangeType.ty go.any`, which matches `FmtArg.val`. Go's `handleMethods` calls `String` only for `%v %s %x %X %q`, and `String` is assumed total anyway. |
| P-F3 | `ConfState.Equivalent`: the mismatch branch formats `*ConfState`s | **Resolved; open decision C35.** | `FmtArg.confState` (`confStatePts` at any fraction, given back). The clones, `confStateFull` at `own 1`, reach `confStatePts` through the unfold laws. Reading `sizeCache` by reflection is not undefined behaviour in Go's memory model (a racing read of a word sees some write). The header states this assumption explicitly. |
| P-F4 = C-F3 | No law ties `bootEntryData` to `proto.Marshal`'s output | **Resolved.** | `noMaps_raftpb.spec` and `bootEntryData_marshal.spec` (`raftpb/Api.lean`). `RawNode.Bootstrap` (`bootstrap.go:54-55`) gets `msgAt ∗ bootCC` from `bootCC_lit`, and `fits`/`marshalOk` from `bootCC_facts`' `confChangeV1Is`. `Marshal.spec` then gives `bs = marshalOut` (by `noMaps`), which equals `bootEntryData`. This is consistent with `bootCC_facts`' `encodes` (`marshalOut_encodes`) and with R1's `bootEntryData_decode`. `ReqBootstrapBytes` is unblocked. |
| P-F5 | `ReqConflictHint` assumed no `ErrCompacted` below the hint | **Resolved.** | `reads.go:59-62` skips `ErrCompacted`. `findConflictByTerm`'s post gives `termOf j = some tj > term` on `(r, index]`, so `term(j)` returns either `nil` with `tj`, or `ErrCompacted` (skipped). |
| P-F6 | `ReqMoveBeforeAdvance` compacted with no stored snapshot | **Resolved, except N1(b).** | `CreateSnapshot(i, cs, nil)` comes before `Compact`. `logStor_createSnapshot`'s COMM gives `logSnapLb i` in both outcomes. `raftLog_publish` gives `logFloor i` once `absorb` has cleared `handing`, and `logFloor_stored` gives `logStored`. The no-pending-snapshot and log-matching assumptions were added. |
| P-F7 | `proto.Uint64` in the raftconf snippets | **Resolved.** | `raftconf/confchange.go:13` uses `new(id)`. |
| P-F8 | `ReqLearnerFlag` read `trk.Learners` | **Resolved.** | The snippet now reads through `ProgressTracker.LearnerNodes.spec`, whose sorted list `contains` scans. The snippet's sortMax assumption covers `LearnerNodes`' premise: a demotion goes to `LearnersNext`, not `Learners`. |
| C-F1 | `MessageType.String` had no spec, yet rafthttp calls it | **Resolved.** | Assumed specs of `MessageType`, `ConfChangeType` and `EntryType` `.String` were added. The receiver form `x @!! MessageType.ty @!! "String"` matches the translation (`rafthttp.lean:1082`: `MethodResolve MessageType.ty "String"` on `GetType()`'s value). |
| C-F2 | `ProgressTracker.ConfState` returned `confStatePts` where Go builds a full `ConfState` | **Resolved.** | It now returns `confStateFull`. That passes through `switchToConfig`, `raft.applyConfChange`, `RawNode`/`node.ApplyConfChange` and etcd's `raftNode.ApplyConfChange`, to `MemoryStorage.CreateSnapshot`'s premise and to `createMergedSnapshotMessage` (`confStateFull … DFrac.discard`). `Clone` gives `mergeDst (norm c)`; `raftpb_norm` and `confStateFull_msgAt` close the merged-snapshot step. |
| C-F4 | `msgRecv` had no introduction law | **Resolved; open decision C36.** | `msgRecv_intro`: from `mergeDst ∗ ⌜msgIs c m⌝`, an update gives `msgRecv`. `Unmarshal` gives `mergeDst t p c ∧ norm c = c ∧ encodes`. With `msgEncodes`, `encodes_fun` (up to `norm`) and `raftpb_norm`, that gives `msgIs c m`. `Clone` gives `mergeDst (norm c)`. Both are true of protobuf-go: `Unmarshal` decodes into fresh allocations, and `Clone` appends into `nil` slices. rafthttp's decoders, `Process` and `raftNode.Step` now carry `msgRecv`. `msgRecv_lend` is realizable: the kept half of the `Entries` field pins the slice. |
| C-F5 | `msgPts` cannot hold `Responses`, so two R1 posts were false | **Resolved; open decision C37.** | `msgOut` (`msgCore ∗ msgResps`), and `msgOut_nil` with `msgPts`. Both helpers now return `∃ rs, msgOut p (own 1) mm rs`, which is true at every call. |

Second tier of the original reports:
- **Resolved:** S1 (`loggerOk` added to `unstable`'s realization), S2 and S3 (snippet `Assumes`), S4
  (`ReqCloneFresh` ranges over the fresh `IDs()`; `JointConfig.IDs.spec`'s pointer receiver matches
  `Code/…/v3.lean`), S5 (header names `Proto.mergeDst`), and C's sortMax header (`quorum/Api.lean:45-54`).
  The `MemoryStorage.firstIndex`/`lastIndex` specs are back (R1's).
- **Not re-checked:** C's "log laws reached only through prose".

## Regressions and new laws

Every spec in the area that changed since `1aa6fc1337` still closes from its callees as they are
now:
- the `Equivalent` sketch, in both directions;
- `MarshalConfChange`'s decode step, through `norm`;
- `ProgressTracker.ConfState`'s fresh `AutoLeave` cell (`confStateGo … true`);
- the `Changer.apply` sketch.

I checked the new laws against 2a's `proto` text and protobuf-go v1.36.12:
- **`raftpb_norm`: plausible and not vacuous.** raft.proto is `proto2` (`raft.proto:1`), so every
  scalar and `bytes` field has explicit presence.
  - protobuf-go sets `isPointer = repeated || HasPresence` (`codec_message.go:136`).
  - Its merge skips only `nil` sources (`merge.go:75`).
  - `mergeBytes` copies a set, empty field as non-`nil` (`merge.go:187`).
  - A repeated field merged from an empty source stays `nil`.

  So `norm` erases only `nil` versus empty repeated fields. raftpb's models are `List`s and do not
  see that. The realization is to define every reader as reader∘`norm` (`norm` is idempotent by
  `norm_facts`).
- **`confState_ext`: true.**
  - `confStateIs … true` fixes the lists (in order) and `AutoLeave`'s value and presence.
  - `plain` excludes unknown fields.
  - ConfState has no other fields.
- **`noFloats_raftpb` and `noMaps_raftpb`: true of `raft.proto`.**
- **`bootEntryData_marshal`: consistent.**
  - It is stated for every `ctx`, but `bootCC_lit` is the only source of `bootCC`, and it needs
    `ctx ≠ []`. R1's `BootLog` also requires non-empty contexts. etcd's contexts are JSON, and no
    example bootstraps through `StartNode`.
  - `decodeConfChange`'s `Classical.choose` is well defined up to `norm`, by `raftpb_norm` (the
    readers are functions).
- **ApiLog: `logStored`, the `logStor_append` COMM, and `raftLog_storedStable` are plausible.**
  Their realization: a committed index is rewritten only with the same entry, and `restore` needs
  `s.index > committed`. The `LogState.floor` field and the new `Wf` conjunct `floor ≤ applying`
  are kept by every R3 function: `appliedTo` only raises `applying`, and `restore` only raises
  `committed`.

## New first-tier findings

**N1 (R3 snippets, `examples/specreq/raftlog/`): two premises that other groups' repairs added are missing from the snippets' `Assumes`.**

- **(a) `floor ≤ applied`.**
  - **What changed.** A4 P3 / C32 made `compactFloor = max base (max applied floor)`
    (`ApiLog.lean:283-285`). `Wf` only bounds `floor ≤ applying`, so a state with
    `applied < floor` satisfies `Wf`.
  - **`ReqScanConfChanges`** (`reads.go:89-98`) calls
    `scan(applied+1, …)`. `raftLog.scan.spec` requires `compactFloor < lo`, but its `Assumes` give
    only `applied ≥ base`. R2's `hasUnappliedConfChanges.spec` added exactly this premise
    (`⌜o.log.floor ≤ o.log.applied⌝`); the snippet did not.
  - **`ReqCompactApplied`** (`ready.go:72-85`) panics if `term(i)` at `i = applied` answers
    `ErrCompacted`. `raftLog.term.spec` admits that whenever `i < compactFloor`, which includes
    `applied < floor`.
  - **Fix.** Add to both `Assumes`: "no floor published above `applied` (not between `Advance`'s
    rendezvous and its apply acknowledgement: R2's `coreIdle_floor`)".
- **(b) `cs` full.**
  - **What changed.** `MemoryStorage.CreateSnapshot.spec` now takes `RaftPb.confStateFull`.
  - **The gap.** `ReqCompactApplied` and `ReqMoveBeforeAdvance` pass a caller's
    `cs *pb.ConfState`, but their `Assumes` say only "valid" or "the configuration at …". The
    raftnode snippets were updated ("`confStateFull`"); these two were not.
  - **Fix.** Add "`cs` is full (`AutoLeave` set: as `ConfState()`/`ApplyConfChange` return it)".
    Also add `logFloor_stored.spec` to `ReqCompactApplied`'s `Specs`/laws line:
    `logStor_createSnapshot` now takes `logStored`.

## Second tier (new)

- **`raftpb/ReqBootstrapBytes` has no size bound on `ctx`.** `Marshal.spec` needs `c.fits`, and
  `encSize ≤ 64 + |ctx|`. `ReqMarshalDecode` assumes `|ctx| < 2^40`; add the same assumption here.
- **`FmtErrorf.lean` is admitted under every verb.** That is broader than either call site needs
  (`%d` and `%+#v`). It is true as argued, but a narrower boundary (the verbs used) would be less to
  trust. This belongs to C35.

## Counts

- **Original first-tier findings:** 13 entries, 12 distinct (P-F4 = C-F3).
  - Resolved: 12. Four of them depend on open decisions: P-F2 and P-F3 on C35, C-F4 on C36, C-F5
    on C37.
  - P-F6's snippet still lacks N1(b).
- **Spec files re-checked** (changed since `1aa6fc1337`): 18 closes of 18.
  - 14 in the area: ApiLog, DescribeConfChange, quorum/Api, Changer.apply, ProgressTracker.ConfState,
    and nine in raftpb (Api, Model, FmtErrorf, the three `String`s, ConfChangesToString, Equivalent,
    MarshalConfChange).
  - 4 in 2a's `proto`, as callees.
  - Also checked: 9 consumers outside the area (the `confStateFull` and `msgOut` chains,
    `CreateSnapshot`).
- **New laws checked:** 13, all plausible and not vacuous.
  - raftpb (9): `raftpb_norm`, `confState_ext`, `noFloats_raftpb`, `noMaps_raftpb`,
    `bootEntryData_marshal`, `msgRecv_intro`, `msgRecv_lend`, `msgOut_unfold`, `msgOut_nil`.
  - ApiLog (4): `raftLog_storedStable`, `logFloor_stored`, the restated `raftLog_publish`, and
    `logStor_append`'s COMM.
- **Snippets re-checked** (changed, or affected by a changed spec): 17, of which 14 close.
  - Do not close (N1): `ReqScanConfChanges`, `ReqCompactApplied`, `ReqMoveBeforeAdvance`.
- **Go bugs:** none found.
