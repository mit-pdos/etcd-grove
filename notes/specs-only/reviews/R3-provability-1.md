# R3 (raft's log): provability review, round 1

Reviewer: provability agent, 2026-11-09. Read: `SpecPlan/Spec/go_etcd_io/raft/v3/ApiLog.lean` and every R3
spec (`raftLog__*`, `unstable__*`, `readOnly__*`, `newLogWithSize`, `newReadOnly`, util/types
helpers), R1's `Model.lean`/`Api.lean` (storage contract, `memStor`, `stor_*`, `readyStor_*`) and
the `MemoryStorage__*` specs, R2's `ApiCore.lean`, `node__Advance.lean`, `batch-R2.md` and the
`req/` files, the snippets `examples/specreq/raftlog/*.go`, the pinned Go (`.lake/src/raft/{log,
log_unstable,read_only,util,types,raft,rawnode,node,storage}.go`, `raftpb/confstate.go`) and the
old specs (`specs-ref`). I read `notes/specs-only/batch-R3.md` only after my findings; its open
questions are answered at the end. I built nothing.

What is good: one `raftLog l ls` over a Go-shaped, transparent `LogState` is a large simplification
of the old window predicates; the read specs compute exactly what Go computes (`lastIndex`'s odd
state after `stableTo` with a snapshot pending is modelled, not hidden); concurrent compaction is
inside the read specs with a uniform margin (`compactFloor`) and the `logCompactedLb` witness that
makes `IsEmptySnap` provably false in `maybeSendSnapshot` (`ReqSendOrSnapshot` goes through);
the storage-write laws state what raft guarantees at each write and their outer mask `⊇ ↑N`
instantiates R1's `⊤`; `acceptUnstable`'s `handing = false` premise matches the sync `Ready`
discipline; `readOnly` and the util helpers mirror the code. I checked the ErrCompacted margins of
`term` (log.go:387-413), `slice`/`mustCheckOutOfBounds` (log.go:499-565), `entries`, `matchTerm`,
`maybeCommit`, `findConflict(ByTerm)`, `firstIndex`, `lastEntryID` and `nextCommittedEnts`: under
the realization's invariant (`σ.off` at most a floor, floors at most `compactFloor`, `σ.off ≤
σ.snap.index`) each disjunct is what Go returns, and the read-then-read races (firstIndex, then
lastIndex, then `Storage.Term`) stay inside them. `isStorage`'s preconditions (`j ≤ σ.last`,
`hi ≤ σ.last + 1`) hold at each storage call provided the pending batch never truncates the storage
below the stable index, which is exactly what F2 below breaks.

## First tier

### F1. `raftLog_publish` is too strong: R2 cannot give R1's `Advance` its `appliedLb` (ApiLog.lean:574-577)

`raftLog_publish` needs `ls.us.snap = none` and `i ≤ ls.stable`. R3's own mapping (req
`go_etcd_io_raft_v3.md`, "from R3" item 2) realizes `appliedLb n i` as `∃ t, logFloor l i t`, and
R1's `node.Advance.spec` (node__Advance.lean:56) and R2's `ackPost` (ApiCore.lean:219-222) give
`appliedLb rn st.delivered.length` after every `Advance`. With synchronous writes the committed
entries a `Ready` hands out may still be unstable (`nextCommittedEnts(rn.applyUnstableEntries())`,
rawnode.go:144, `applyUnstableEntries = !asyncStorageWrites`), and `node.run` steps `recvc`
messages while `advancec` is armed (node.go:394, 438, 443). Two reachable cases leave the applied
index above what `publish` accepts at `Advance`:

- a message of a higher term arrives between `acceptReady` and `Advance` (`becomeFollower`); the
  queued `MsgStorageAppendResp` carries the old term and its `Index` is ignored (raft.go:1180-1190),
  while the `MsgStorageApplyResp` (term 0) still runs `appliedTo` (raft.go:1223-1227): `applied >
  stable`;
- a `MsgSnap` arrives in between and `restore` succeeds: `us.snap ≠ none` at the `appliedTo`.

Compacting the storage to such an applied index is safe (the storage holds the written committed
entries; raft reads the unstable part first, log.go:391, 506), so the premise, not the code, is
the problem. Restatement: publish any `i ≤ ls.applied` (hence `≤ committed`) whose stored entries
are the log's, e.g. `i ≤ ls.applied → ls.handing = false → (i ≤ ls.base ∨ (i ≤ ls.base +
ls.stored.length ∧ ls.stored.take (i - ls.base) = ls.log.take (i - ls.base))) → ls.termOf i = some
t ∨ i = ls.base ...`, and weaken the realization's "floor ≤ stable" to "floor ≤ `σ.last`, the
storage's entries through the floor committed" (the `σ.off > stable` state that results is
harmless: `slice` then takes the unstable path, log.go:506). Affects: R2's realization of
`appliedLb`, hence R1's `node.Advance`, `RawNode.Advance`, `stor_compact`, `stor_createSnapshot`.

### F2. `StableOk` admits `stableTo` while a handed-out batch is unwritten; the specs are then jointly unrealizable (ApiLog.lean:381-383)

`StableOk` constrains only `ls.stored`; it does not mention the batch still in flight. Trace, using
only R3's specs: `stored = 1..9 (t2)` absorbed, `offset = 5`, `us.ents = 5..9`, the ack ignored;
`maybeAppend` truncates at 8 with `[8 t3]` (oip 8); `acceptUnstable` hands out `h = ⟨none, 8,
[8 t3]⟩` (`handing = true`); `maybeAppend` truncates at 8 again with `[8 t2, 9 t2]`; `stableTo(9,
t2)`: `StableOk` holds (both conjuncts, since `stored` already has `1..9 t2`), leaving `us.ents =
[]`, `snap = none`. The client then fires `logStor_append` for `h` (its precondition holds):
storage `1..7 t2, 8 t3`, `σ.last = 8`. Now `raftLog.lastIndex.spec` must return `ls.lastIndex =
base + |stored| = 9` while Go reads `storage.LastIndex() = 8` (log.go:311-320), and `term(8)` reads
`t3` where `termOf` says `t2`. No realization satisfies `stableTo`, `logStor_append` and
`lastIndex`/`term` together. Raft never gets there (the second truncation needs a term change, and
the stale ack is then dropped by `Step`, raft.go:1180), but that guard is R2's, invisible to R3's
statements. Restatement: add `ls.handing = false` to `StableOk` (and to `SnapAckOk`, harmlessly).
R2 meets it: acknowledgements are only stepped from `stepsOnAdvance` (rawnode.go:484-488), after
the client's writes (`readyStor … none k []` in `Advance`'s pre) and the absorb. The same flaw makes
`raftLog_storageLastIndex.spec` (ApiLog.lean:546-551) false whenever a batch is written but not
absorbed: add `ls.handing = false` there too (its one caller, `Bootstrap`, has it).

### F3. `unstable.truncateAndAppend`, `raftLog.append`, `raftLog.maybeAppend` dropped the capacity requirement (unstable__truncateAndAppend.lean:32-38)

The adopt arm (`fromIndex <= u.offset`, log_unstable.go:206-212) stores the caller's slice as
`u.entries`; a later append arm (log_unstable.go:203-205, `append(u.entries, ents...)`) writes into
that slice's spare capacity. With only `entriesRO sl k es` in the pre, the realization of `unstable`
cannot own the capacity it later writes, so the adopt case and the next append cannot both be
proved. The old spec had it (`specs-ref` unstable__truncateAndAppend: in the adopt arm `dq =
discard ∗ ownSliceCap Loc es (own 1)`). Restatement: `⌜sl.len = sl.cap⌝ ∨ ownSliceCap Loc sl
(DFrac.own 1)` in `unstable.truncateAndAppend`, `raftLog.append` and `raftLog.maybeAppend` (or only
in the adopt arm). Callers: `appendEntry` passes `cloned` (`make(len, len)`, raft.go:832) and meets
it; `handleAppendEntries` passes `m.Entries[ci-offset:]` of a received message (log.go:127), so R2
needs the received message's `Entries` capacity from R1/3h's `msgPts` (a request to file).

### F4. `isMsgInArray.spec` is false for a negative `MessageType` (isMsgInArray.lean; util.go:54-57)

`i := int(msgt)` sign-extends the `int32` (the translation converts `MessageType.ty` to `go.int`
and compares with signed `GoLt`), so for `msgt < 0` the guard `i < len(arr)` holds and `arr[i]`
panics; the spec returns `(bs[uint.nat t]?).getD false`. The old spec had `0 ≤ sint.Z t`.
Restatement: add `0 ≤ sint.Z t` (or `uint.nat t < 2^31`). R1's `IsLocalMsg.spec`/`IsResponseMsg.spec`
(over every `t : w32`) inherit the problem (R1's to fix: a premise, which `node.Step`/`RawNode.Step`
meet for messages decoded from the wire, since raftpb is proto2 and a closed enum never decodes to
an unknown value). Go: a public function `raft.IsLocalMsg(pb.MessageType(-1))` panics; not reachable
from etcd; a `nonissues/` candidate (documentation only, `blocks-proof: no`). Nothing is recorded
in `issues/` or `nonissues/` yet.

### F5. `slice`, `entries`, `nextCommittedEnts`, `scan` are unprovable against R1 as it stands (raftLog__slice.lean)

`slice` calls `extend(ents, unstable)` (log.go:547) on the storage's slice; `extend.spec` needs
`cap < need ∨ ownSliceCap dst`. R1's `isStorage` `Entries` success case (Api.lean, `isStorage`)
gives only `entriesRO sl lo es`; R3's request (req `go_etcd_io_raft_v3.md`, "from R3" item 1: add
`⌜sl.len = sl.cap⌝`) is not in `Api.lean` at HEAD. True of `MemoryStorage` (storage.go:
`ents[:len(ents):len(ents)]`). Until R1 adds it, the four specs have no proof. (With it, `cap <
need` holds: the unstable part is non-empty on that path, log.go:539.)

### F6. R1's storage laws are not derivable from R3's under the stated mapping (ApiLog.lean:620-625)

R3 claims "`stor_read` ~ `logStor_read`". R1's `stor_read` (Api.lean:825-830) takes `storSnapLb n
j` and guarantees `j ≤ σ.snap.index`, and commits `storSnapLb n σ.snap.index`; `logStor_read`
takes no `logSnapLb` and commits `True`. And its `appliedLb n σ.off` must come from `logFloor l
σ.off σ.offTerm`, which R2 can only connect to its own committed-term records (needed for
`stor_createSnapshot`'s `s.term`) through an agreement law R3 does not export. Restatement: give
`logStor_read` a `logSnapLb l j` input with `j ≤ σ.snap.index` in the AU and `logSnapLb l
(uint.nat σ.snap.index)` at commit (the storage's snapshot index never decreases:
`applySnapshotErr`, `createSnapshot`), and add `logFloor_agree : logFloor l i t ∗ logFloor l i t' ⊢
⌜t = t'⌝` (every floor is at a committed index). Affects R1's realization of `stor_read`,
`stor_createSnapshot`.

### F7. Snippets that are not provable from the specs

- **`ReqReadyCycle`** (ready.go:25-61): the check `l.term(last.GetIndex())` (ready.go:47) sits
  between `stableTo` and `stableSnapTo`. When the `Ready` carries a snapshot and entries after it
  (a follower that restored and then appended), `lastIndex()` is the snapshot's index there
  (log_unstable.go:67-75: entries empty, snapshot set), so Go's `term` returns `ErrUnavailable`
  (log.go:401) and the snippet panics; the spec says the same (`termOf` is `none`). A snippet bug:
  move the check after `stableSnapTo`. Its `Assumes: StableOk holds` also replaces a fact the
  specs should give (S1).
- **`ReqCompactApplied`** (ready.go:69-79): `term.spec` allows `ErrCompacted` for any `i + 1 <
  compactFloor = max base applied`; with `applied > i + 1` (the client compacts at an older
  published floor) the snippet's panic is reachable as far as the specs say. The REQ text
  ("ErrCompacted only below that index") is stronger than any spec; no caller in raft or etcd
  needs it. Fix the snippet (check `term(j)` for `j > applied`, or assume `i = applied`).
- **`ReqConflictHint`** (reads.go:47-60): re-reading `l.term(j)` after `findConflictByTerm` may
  answer `ErrCompacted` under concurrent compaction (`j < compactFloor`); add `index >
  compactFloor` (as both real callers have: `index ≥ committed`, raft.go:1519, 1838) to `Assumes`.
- **`ReqLimitSize`** (util.go:14-24): `got[i] != ents[i]` compares pointers; `limitSize.spec`
  gives `entriesRO sl' k (es.take n)`, which says nothing of `sl'`'s pointers. Either state `sl' =
  slice.slice sl 0 n` in the post or drop the comparison.

## Second tier

- **S1. `Wf` should carry the in-progress agreement** (ApiLog.lean:370-377). To discharge
  `StableOk` even in the plain cycle (`ReqReadyCycle` without other steps), a caller needs
  `stored` to agree with `us.ents` on `[offset, offsetInProgress)` when `handing = false`
  (`absorb` writes `stored` from `h.start = oip`, keeping `stored.take (oip - base - 1)`). `Wf`
  does not say it, so R2 must re-derive it through every transition of the model. It is an
  invariant R3 can prove once (truncation lowers `oip` to `≤ k`, `absorb` re-establishes it);
  add `handing = false → ls.stored.take (oip - base - 1) = ls.log.take (oip - base - 1) ∧ oip - 1
  ≤ base + |stored|` to `Wf`. Then R2 needs only log matching for a matching ack.
- **S2. `absorb` across a `restore`** (ApiLog.lean:342-351). A batch handed out before a `restore`
  (node.run steps a `MsgSnap` between `Ready` and `Advance`) is absorbed with `h.start ≤ base`;
  `h.start - base - 1` truncates to 0 and `stored := h.ents` places old entries after the new base.
  It is overwritten when the new snapshot's batch is absorbed, so no read sees it, but it makes
  `stored` meaningless in that window and `Wf`'s `base + |stored| < 2^64` unprovable at extreme
  values. Restate: drop the entries at or below `base` (`h.ents.drop (base + 1 - h.start)` at
  position `base + 1`), or skip the entries when `h.start ≤ base`.
- **S3. The `2^63` and wrap premises are dischargeable only if R2's bound is chosen for them.**
  R2 (req `go_etcd_io_raft_v3.md`, "from R2", item 5) proposes a cluster step bound below `2^64 -
  1` at `cluster_alloc`. `slice`/`entries`/`scan`/`nextCommittedEnts` need ranges `< 2^63`; with
  every index `< 2^63` (the same receipts) they and the wrap premises (`append`'s `k + |es| <
  2^64`, `maybeAppend`'s `prev + |es|`, `restore`'s `s.index + 1`, `findConflict`'s) follow. R3
  should file this with R2/R1 (it is not in R3's req section). Also make `nextCommittedEnts`'s
  premise conditional (`hi - lo < 2^63 ∨ ls.applyingPaused ∨ ls.us.snap.isSome`): `ReqRestore`
  calls it on a fresh restore, where it returns before slicing, yet must prove the bound.
- **S4. `raftLog_fields`'s wand has no update** (ApiLog.lean:539-542). The realization's
  invariant claims "the stored snapshot's index ≤ committed"; if the invariant tracks `committed`
  in ghost state, closing after a write needs `|==>`. Put the wand's conclusion under `|==>`.
- **S5. Snippet assumptions missing**: `ReqReadIndexQuorum` (readindex.go) must assume `self` and
  `others` cover every voter (or a quorum of each half) and `|voters| ≤ 2^62`, otherwise `N = 0` and
  it panics; `ReqPrevTerm` (reads.go:71) panics at `last.index = 2^64 - 2` (`term(2^64-1)` wraps
  to `ErrCompacted`, log.go:398), guard `last.index < ^uint64(0) - 1`; `ReqStart` omits
  `σ.last + 1 < 2^64` and `σ.off ≤ σ.snap.index`; `ReqRestore`/`ReqReadyCycle` omit the `2^63`
  range bound of `nextCommittedEnts`; `ReqLeaderAppend` relies on no snapshot pending (a leader:
  `promotable`).
- **S6. `nextUnstableSnapshot` returns no validity.** R2 must hand out `snapValid` with the
  `Ready`'s snapshot (R1); returning `□ V s` (with `logStorage`) would save R2 a record keyed by the
  pending snapshot.
- **S7. Cross-batch text.** R1's `Api.lean` intended realization still puts "the attached
  storage's `S σ` in the node's invariant"; with R3's mapping the only owner is the log's
  invariant (`S σ` is exclusive, `memStor` excl): R1 should say `nodeStorage` is `logStorage`.
  R1's `appliedLb` docstring ("applied index at least `i`") no longer matches a floor from an
  install (before `Advance`).
- **Uncertain.** `assertConfStatesEquivalent`'s premise `ConfState.Equiv` ignores unknown fields,
  but `Equivalent` ends in `proto.Equal` (raftpb/confstate.go:48), which compares them: depends on
  whether 3h's `confStatePts` excludes unknown fields. `raftLog.restore`'s `Infof("%s", l)`
  (log.go:467) makes the logger call `(*raftLog).String`, which reads the struct the caller owns:
  whether `loggerOk`'s realization for zap can be proved over such an argument is not settled here.

## The points the brief asked about

- **Two owners of the storage?** No conflict if R1's `nodeStorage n γ S` is realized as R3's
  `logStorage l S (snapValid γ) N` (R3's mapping). The AUs nest correctly: R1's `@ ⊤, ∅` is R3's `Eo
  = ⊤`, and etcd's writes from its own goroutine are AUs over the one invariant, interleaving with
  raft's atomic reads. Gaps: F6 (`stor_read`, floor agreement) and S7 (R1's text).
- **`ErrCompacted` under concurrent compaction**: sound as stated (checked above). It is weak:
  `ReqCompactApplied` and `ReqConflictHint` overclaim against it (F7).
- **`StableOk`/`SnapAckOk`**: they do not make a stale acknowledgement unprovable. A no-op ack
  (`stableTo` ignored) has `ls.stableTo … = ls`, so the first conjunct is reflexive and the second
  is `Wf`'s; `SnapAckOk` is vacuous unless the pending snapshot is at `i`, and then the absorb made
  `snapStored` true. The matching ack needs S1 plus log matching. But `StableOk` forbids too
  little (F2).
- **The author's suspected raft bug (batch-R3.md, question 1): refuted by reading, so no
  `issues/` entry.** `restore(s2)` runs only if `matchTerm(s2.index, s2.term)` is false
  (raft.go:1927-1934: else it fast-forwards `commitTo` and returns). If after `s2` a `MsgApp`
  re-sends `(id, t)` with the handed-out term, log matching says the handed-out log and the new
  one agree through `id`, so the handed-out log (still the node's log until `restore`, since a
  committed entry is never truncated) held `(s2.index, s2.term)` when `s2` arrived: `matchTerm` was
  true, and no restore happened. If `s2.index > id`, `stableTo(id)` is ignored (`id < offset`, the
  index matches no snapshot). Either way R2 discharges `StableOk` (by log matching, or by
  reflexivity). It stays uncertain only in that I wrote no test.
- **`2^63` and wrap premises**: see S3. They are real for the model (`extend`'s `int` sum,
  util.go:334-343; Go's wraps), and dischargeable from a cluster index bound `≤ 2^63`.
- **Snippets panic-free**: `ReqStart`, `ReqLeaderAppend`, `ReqFollowerAppend`, `ReqSendOrSnapshot`,
  `ReqScanConfChanges` (after F5), `ReqRestore`, `ReqReadIndexQuorum` (with S5's assumption),
  `ReqVoteResp`, `ReqPayloadSizes`, `ReqConfStatesEquivalent` go through, given the requested
  raftpb law `entriesRO ⊣⊢ ∃ ps, sl ↦*□ ps ∗ [∗list] entryRO`. `ReqReadyCycle`,
  `ReqCompactApplied`, `ReqConflictHint` and `ReqLimitSize` do not (F7).

## Targets ranked by need of revision

1. `ApiLog.lean`: `StableOk` (F2), `raftLog_publish` (F1), `logStor_read` plus `logFloor_agree`
   (F6), `raftLog_storageLastIndex` (F2), `Wf` (S1), `absorb` (S2), `raftLog_fields` (S4).
2. `unstable__truncateAndAppend`, `raftLog__append`, `raftLog__maybeAppend` (F3).
3. `isMsgInArray` (F4).
4. `raftLog__slice`, `raftLog__entries`, `raftLog__nextCommittedEnts`, `raftLog__scan`: blocked on
   R1 (F5); `nextCommittedEnts`'s premise (S3).
5. Snippets `ready.go`, `reads.go`, `util.go`, `readindex.go`, `append.go` (F7, S5).
6. `raftLog__stableTo`, `raftLog__stableSnapTo`, `raftLog__nextUnstableSnapshot` (through F2, S6).
7. No change needed: `raftLog__{term, firstIndex, lastIndex, lastEntryID, matchTerm, maybeCommit,
   findConflict, findConflictByTerm, commitTo, appliedTo, acceptApplying, acceptUnstable, restore,
   snapshot, isUpToDate, zeroTermOnOutOfBounds, mustCheckOutOfBounds, has*}`, the other `unstable__*`,
   `readOnly__*`, `newReadOnly`, `newLogWithSize`, `voteRespMsgType`, `entsSize`, `limitSize`
   (beyond F7's optional prefix), `payloadSize(s)`, `extend`, `pbEntryID`, `DescribeConfChange`,
   `assertConfStatesEquivalent` (uncertain point above).

## Verdict

Not ready. The vocabulary's shape is right, and most read and helper specs are true of the code.
Four hard-rule problems need repair before R2 can build on it: `StableOk` lets R3's own specs
contradict each other (F2); `raftLog_publish` cannot give R1's `Advance` its `appliedLb` (F1); the
capacity requirement of the adopting append was dropped (F3); `isMsgInArray` lost its sign premise
(F4). Two are cross-batch: the `Entries` capacity request R1 has not met yet (F5), and the R1
storage laws R3's mapping does not reach (F6). Four snippets do not go through (F7). Each fix is
local: a premise, a law, or a snippet edit.
