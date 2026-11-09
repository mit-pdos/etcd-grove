# R3 (raft's log: raftLog, unstable, readOnly, util.go): completeness review, round 1

Reviewer: completeness, independent of the author. Read: `Spec/go_etcd_io/raft/v3/ApiLog.lean`, every
R3 spec file (`newLogWithSize`, `raftLog__*`, `unstable__*`, `newReadOnly`, `readOnly__*`, the
util.go/types.go helpers), the snippets `examples/specreq/raftlog/*.go`, the callers in the pinned
raft (`.lake/src/raft/{raft,rawnode,node,status,bootstrap}.go`), etcd's server
(`.lake/src/server/etcdserver/{raft,server}.go`, and through `go/pkg/mod`), R1's `Api.lean` (the node
predicates R3's laws are meant to realize: `appliedLb`, `storSnapLb`, `stor_*`, `readyStor_*`), R2's
`ApiCore.lean` (`ackPre`/`ackPost`) and the R2 specs that call the log. I read
`notes/specs-only/batch-R3.md` only after forming the findings below; where the author already
raised a point as an open question I say so. Line numbers are the pinned sources'.

## Users and patterns

Outside the log's own files, the log, `readOnly` and the helpers are called only from raft.go,
rawnode.go, bootstrap.go and status.go (node.go: none). etcd and the examples reach them only
through R1's node predicates (the `stor_*`/`readyStor_*` laws are realized from R3's `logStor_*`,
`req/go_etcd_io_raft_v3.md`, "from R3", item 2); no external caller of `DescribeConfChange`,
`IsLocalMsg`, ... (grep of the server and `examples/`).

| # | pattern (what the caller relies on) | call site | snippet | verdict |
|---|---|---|---|---|
| L1 | start: log at the storage's compaction point, `InitialState` while starting, `lastEntryID` known, `loadState` raises `committed`, `appliedTo(c.Applied)`, attach | raft.go:443-486, 2039-2042 | `ReqStart` | covered (attach, `appliedTo(Applied)` not exercised: S6) |
| L2 | leader appends its proposals at `lastIndex+1`, new last index; commits a quorum-matched entry of its term | raft.go:831-852, 796 | `ReqLeaderAppend` | covered |
| L3 | follower `maybeAppend` after a matching prev (entries at `prev+1, ...`), commit `min(commit, lastnew)`, else reject with a hint | raft.go:1809-1845 | `ReqFollowerAppend` | pre not establishable: **F2** |
| L4 | heartbeat commit `commitTo(m.Commit)` (panics past `lastIndex`) | raft.go:1851 | none (listed in `ReqFollowerAppend`'s Users, not called) | S6 |
| L5 | probe hints `findConflictByTerm` (liveness only) | raft.go:1519, 1839 | `ReqConflictHint` | covered (snippet: S5) |
| L6 | send: `term(Next-1)`, `entries(Next, maxMsgSize)` non-empty below the end; `ErrCompacted` leads to a non-empty, valid `snapshot()`; `ErrSnapshotTemporarilyUnavailable` gives up | raft.go:620-690 | `ReqSendOrSnapshot` | covered; `2^63` premise has no source: **F3** |
| L7 | votes: `lastEntryID`, `isUpToDate(cand)` (the election restriction) | raft.go:1081,1125,1179,1238-1240 | none | **S1** |
| L8 | `committedEntryInCurrentTerm`: `zeroTermOnOutOfBounds(term(committed)) == Term` means an entry of the term is committed | raft.go:2070 | `ReqPrevTerm` calls it, checks nothing | S6 |
| L9 | Ready hand-out: `nextUnstableEnts`, `nextCommittedEnts(true)`, `hasNextUnstableSnapshot`/`nextUnstableSnapshot`, `hasNextOrInProgressUnstableEnts`, `lastEntryID` for the ack; `acceptUnstable`, `acceptApplying(last, entsSize, true)` | rawnode.go:140-160, 274-355, 425-436, 457-463 | `ReqReadyCycle` | covered |
| L10 | acknowledgement at `Advance`: `stableTo(id)`, `appliedSnap` (`stableSnapTo`, `appliedTo(index, 0)`, `lastIndex`), `MsgStorageApplyResp` (`appliedTo(last, entsSize)`, `payloadsSize`); the applied index becomes a compaction floor (R1/R2's `appliedLb`) | raft.go:1215-1228, 736-790 | `ReqReadyCycle` (only the case where nothing moved between `Ready` and `Advance`) | **F1**; author's OQ1 (**F4**) |
| L11 | the client's storage writes and reads: install, append, `CreateSnapshot`/`Compact` at an applied index, `Snapshot()` read | etcdserver/raft.go:287,292; server.go:755, 2132, 2180 | `ReqReadyCycle`, `ReqCompactApplied` | install/append/compact/create covered; `stor_read` not realizable: **F5** |
| L12 | snapshot received: `matchTerm` fast-forward with `commitTo`, else `restore`; pending until stored | raft.go:1877-1945 | `ReqRestore` | covered |
| L13 | `promotable` (`hasNextOrInProgressSnapshot`), `hasUnappliedConfChanges` (`scan(applied+1, committed+1, maxApplyingEntsSize)`) | raft.go:997-1040, 1949 | `ReqScanConfChanges` | covered; `2^63`: F3 |
| L14 | field reads (`committed`, `applied`, `maxApplyingEntsSize`), `lastIndex` for progress, `pendingConfIndex`, `confchange.Changer.LastIndex` | raft.go passim, status.go:63 | `ReqStart` (fields) | covered |
| L15 | `Bootstrap`: `storage.LastIndex()` through the field, `append` on an empty log, `committed = len(ents)` | bootstrap.go:36-77 | none | S6 |
| L16 | read index (Safe): `addRequest(committed, m)`, own `recvAck(id, heartbeatCtx())`, `bcastHeartbeat(heartbeatCtx())`, `recvAck(from, echo)`, `maybeAdvance(Voters)` in order, once | raft.go:725, 1611-1625, 2159-2166 | `ReqReadIndexQuorum` | covered |
| L17 | `reset` drops the queue (`newReadOnly(r.readOnly.option)`); `option` read | raft.go:827, 1615, 1765 | none | S6 (minor) |
| L18 | helpers: `voteRespMsgType`, `payloadSize(s)`, `entsSize`, `limitSize` (storage reads), `assertConfStatesEquivalent`, `DescribeConfChange` (log line), `isMsgInArray` (R1's `IsLocalMsg`...) | raft.go:479,787,1077,1270,1279,1358; storage.go:161 | `util.go` | covered |

## What is good

- **One Go-shaped model, exact reads.** `LogState`/`UnstableState` with `lastIndex`, `termOf`,
  `maybeTerm`, `nextEntries`, ... computed as Go computes them (the `stableTo`-with-a-snapshot window
  included) means every read spec is "returns the model's value", and every caller-side argument
  (the leader's `li + len`, `ReqRestore`'s last entry, `isUpToDate`, the scan's coverage) is pure
  arithmetic on a transparent model. I checked each read spec against log.go:109-570; they match.
- **Concurrent compaction is in the specs, with the evidence a caller needs**: every `ErrCompacted`
  (`term`, `slice`, `entries`, `mustCheckOutOfBounds`) carries `logCompactedLb`, and `snapshot()`
  returns a snapshot at or past every such index, which is exactly what `maybeSendSnapshot`'s
  "need non-empty snapshot" panic (raft.go:681) needs. `ErrCompacted` is confined below
  `compactFloor`, so `matchTerm`/`maybeCommit`/`maybeAppend` above `committed` are exact.
- **The storage writes are the client's, with raft's guarantees inside the atomic updates**:
  `logStor_compact`'s `i ≤ σ.last` is precisely what `MemoryStorage.Compact` needs not to panic, and
  it is what etcd's `compactRaftLog` (server.go:2176-2187) relies on; `logStor_install`'s COMM
  floor at the snapshot covers the install path.
- **Starting** (`logStarting`, `raftLog_borrowStarting`, `logFresh_attach`) fits newRaft's real order
  (newLogWithSize, then `InitialState` on the same storage, raft.go:443-444).
- The read-index queue specs match this fork's position-based `readOnly` (read_only.go:49-105),
  including the slice-bound premise of `maybeAdvance` (`ackOf v ≤ position`), which is what keeps
  `unconfirmedReads[:N - confirmed]` in bounds.
- The author found a probable raft bug by writing `StableOk` (OQ1) and recorded the short-context
  `recvAck` panic (`nonissues/raft-heartbeat-resp-short-context-panic.md`).

## First tier

### F1. `raftLog_publish` cannot give the applied floor that R2's `ackPost` (and R1's `node.Advance`) promise after the log moved between `Ready` and `Advance`

`ApiLog.lean:574-577`: `raftLog_publish` needs `ls.us.snap = none` and `i ≤ ls.stable`. The only
other sources of a `logFloor` are the attach, the install's COMM and `logStor_read` (at the
storage's compaction point). R1 maps `appliedLb n i` to `∃ t, logFloor l i t`
(`req/go_etcd_io_raft_v3.md`, from R3, item 2), and R2's `ackPost` (`ApiCore.lean:221-222`) gives
`appliedLb rn st.delivered.length` when it steps `MsgStorageApplyResp`, which R1's
`node.Advance.spec`/`RawNode.Advance.spec` pass to etcd (its `CreateSnapshot`/`Compact`,
server.go:2132, 2180). Under `node`, `run` keeps stepping `recvc` while the client handles a
`Ready` (node.go:354-394), so two reachable cases break the premises:

1. **Truncation between `Ready` and `Advance`** (`i ≤ stable` fails). A follower's `Ready` hands
   out entries 5..10 for storage and 5..7 to apply (`nextCommittedEnts(true)`: committed 7, all
   unstable). Before `Advance`, a new leader's `MsgApp` replaces 9..10 (`truncateAndAppend`,
   offsetInProgress := 9). At `Advance`: `stableTo(10, old term)` is ignored (log_unstable.go:138-157),
   so `stable` stays 4; `appliedTo(7)` makes `applied` 7. `ackPost` must give `appliedLb rn 7`,
   i.e. `logFloor l 7 t`, but `7 ≤ stable = 4` is false. Go is fine here: the storage holds 5..10
   (the client wrote them), and compacting to 7 breaks no read (`term(5..7)` answers from
   `unstable` first, `slice` below the floor may answer `ErrCompacted`).
2. **A newer snapshot restored between `Ready` and `Advance`** (`snap = none` fails). The `Ready`
   hands committed 5..7 to apply; before `Advance` a `MsgSnap` at 20 > committed is restored
   (raft.go:1937). At `Advance`, `appliedTo(7)` (`7 ≤ committed = 20`), but `s2` is pending, so no
   floor at 7 can be published; and `restore` set `stored := []`, so raft's ghost no longer even
   knows the storage holds 7. Go is fine: compacting the old storage to 7 is harmless, and the later
   `ApplySnapshot(s2)` replaces it.

(The same applies to `ackPost`'s `appliedLb rn s.index` for an acknowledged snapshot `s1` when a
newer `s2` is pending; there the install's COMM `logFloor` exists, but R1's `readyStor_install`
COMM drops it, so it has to be carried in `readyStor`'s realization to the ack.)

Caller affected: R2's `raft.Step` with `StepSrc.ack` (`ackPost`), hence R1's `node.Advance`/
`RawNode.Advance` and every etcd compaction proof. Snippet: none exercises a step between the hand-out
and the acknowledgement. Suggested fix: make the floor depend on what the storage is known to hold,
not on `stable`/no-pending-snapshot: e.g. keep a ghost "written-through" index in `LogState` that
`absorb` raises (the written batch's end where it agrees with the log at or below `committed`) and
`restore` does not reset, and let `raftLog_publish` take `i ≤ ls.applied ∧ i ≤ written ∧` the term
known at `i`; re-check the invariant's "floor at most the stable index" clause, which the Go reads do
not need (I traced `term`, `slice`, `firstIndex`, `mustCheckOutOfBounds` with `σ.off > stable`).
Alternatively R1/R2 weaken `appliedLb` at `Advance` to what can be published, but then etcd cannot
compact after such an `Advance`. Add a snippet `ReqTruncateBeforeAdvance` / `ReqRestoreBeforeAdvance`
(hand out, step a `MsgApp`/`MsgSnap`, acknowledge, then `CreateSnapshot`+`Compact` at the applied
index).

### F2. `maybeAppend`'s `entriesRO a.entries' (prev+1) es` has no source at `handleAppendEntries`

`raftLog__maybeAppend.lean:346` takes the `MsgApp`'s entry slice as `entriesRO` at indices
`prev+1, prev+2, ...` (each entry's `Index` field; Go's `findConflict` uses `pbEntryID(ents[i])`,
`append` uses `ents[0].GetIndex()`, log.go:133-165). At raft.go:1809-1815 the caller has
`logSliceFromMsgApp`'s post, which does not name `a.entries'` at all
(`logSliceFromMsgApp.lean`, Margin: "the entries' slice is not named"), and `msgPts ml dq m` over
R1's `Msg`, whose `entries : List LogEntry` has no indices (`Model.lean:106-110, 267-280`). So
neither the slice nor its `Index` fields are reachable: `msgSent γ m` cannot say "entry `j` is at
`m.index + 1 + j`" about a field the model drops, and the wire round trip (rafthttp, R1's req to 3h)
then does not preserve it either. Same gap, smaller, at `MsgStorageApplyResp` (raft.go:1225-1227:
`m.GetEntries()[len-1].GetIndex()`, `entsSize`, `payloadsSize` need `entriesRO` of the ack's
entries). Caller affected: R2's `handleAppendEntries` (the follower's whole append path), the apply
acknowledgement. Suggested fix (cross-batch, write it in `req/`): give `Msg` the entries' first index
(or index each entry), have `msgPts` expose `entriesRO entsSlice m.entsFrom m.entries` (3h's
splitting law R2 already asked for), have `msgSent` of a `MsgApp` state `entsFrom = index + 1`, and
have `logSliceFromMsgApp`'s post name `ls.entries'` as that slice. `ReqFollowerAppend`'s `Assumes:`
should then state the consecutive indices it relies on.

### F3. The `< 2^63` range premises have no source at their callers (author's OQ2, recorded)

`raftLog.entries` (`lastIndex + 1 - i < 2^63`), `nextCommittedEnts` (`hi - lo < 2^63`), `scan`,
`slice`: R2's `raft.maybeSendAppend.spec`, `raft.hasUnappliedConfChanges.spec` and
`RawNode.readyWithoutAccept.spec` take no such premise and `raftCore`'s realization states no bound
(`ApiCore.lean:67-70` only says indices are bounded by step receipts, "open question"). As it stands
L6, L9 and L13 are not served. Recorded as the author's open question 2, so not blocking by the
README's rule; my suggestion for the question: the index bound R2 already plans (each appended entry
costs a step, the adequacy theorem's step bound entering at R1's `cluster_alloc`) is the single source
if it is stated as `lastIndex < 2^63` rather than `< 2^64`: every range of indices is then `< 2^63`,
and it also discharges OQ3's wrap premises (`append`'s `k + |es| < 2^64`, `restore`'s, `maybeAppend`'s)
from one fact. Keep the premises where they are (local), and write the bound's form into R2's
`req/` section so that R2 does not choose `2^64`.

### F4. The suspected `stableTo` gap bug is not recorded (author's OQ1), and R2's ack step depends on it

I checked the author's scenario against the code and it looks real: after `restore(s2)` between a
`Ready` (carrying `s1` and entries `(s1, id]`) and its `Advance`, a `MsgApp` re-sending `(s2, id]` at
the same terms makes `unstable.stableTo(id)` fire (`id.index ≥ offset = s2+1`,
log_unstable.go:138-163), so the next `Ready` hands out `s2` with the entries after `id` only;
`MemoryStorage.ApplySnapshot(s2)` resets the storage to the dummy at `s2` (storage.go:234-235), and
`Append` from `id+1 > s2+1` hits `Panicf("missing log entry ...")` (storage.go:322). Spec-wise:
`StableOk` is false there, and R2's `ackPre` (`ApiCore.lean:208-211`) has no premise excluding it,
so `raft.Step(MsgStorageAppendResp)` is not provable as stated. CLAUDE.md asks for a record "as soon
as it is found": a `nonissues/` entry now (code reading), an `issues/` entry with a test when there
is one, and the premise or scope restriction that R2 takes for it named there. Not recorded under
`issues/` or `nonissues/` (checked: `raft-async-snapshot-during-apply-divergence` and
`raft-snapshot-during-apply-stale-confchange` are different paths).

### F5. `logStor_read` does not realize R1's `stor_read`

R3 states the mapping `stor_read ~ logStor_read` (`req/go_etcd_io_raft_v3.md`, from R3, item 2).
R1's `stor_read.spec` (`Api.lean:825-830`) takes `storSnapLb n j` and gives, in the AU,
`j ≤ σ.snap.index`, and in its COMM `storSnapLb n σ.snap.index`. `logStor_read.spec`
(`ApiLog.lean:620-625`) takes no `logSnapLb`, states no lower bound on `σ.snap.index`, and its COMM
is `True`. Caller affected: etcd's `raftStorage.Snapshot()` (server.go:755) and the examples'
storage reads through R1. Fix: `logStorage l S V N ∗ logSnapLb l j ⊢ AU <{ ∃∃ σ, S σ ∗
⌜σ.off ≤ σ.snap.index ∧ j ≤ σ.snap.index⌝ ∗ logFloor l σ.off σ.offTerm ∗ (⌜σ.snap.isEmpty⌝ ∨ V
σ.snap) }> <{ S σ, COMM logSnapLb l σ.snap.index }>` (the invariant's snapshot authority gives both).

## Second tier

- **S1. The election restriction has no snippet** (L7). `isUpToDate`'s spec is exact
  (`raftLog__isUpToDate.lean`), but no snippet relies on it: add `ReqVoteUpToDate` (a voter grants
  only if `(their.term, their.index)` is at least `lastEntryID()`'s, and a granted candidate's last
  term is at least every term in the voter's log, which follows from `termOf` monotonicity the R2
  invariant keeps). The vote is a safety argument; it should have its pattern pinned.
- **S2. `acceptUnstable`'s `ls.handing = false` hard-codes one batch in flight.** Sound and
  sufficient under R1's `ConfigOk` (`AsyncStorageWrites` off), but async writes would need a queue of
  hand-outs in `LogState` and every ack spec restated. The scope is filed in `ConfigOk`'s docstring;
  name this cost in the batch report so the choice is visible.
- **S3. `maybeAdvance`'s `(elements s0).length ≤ 2^62`** (`readOnly__maybeAdvance.lean:46`): the
  sort's limitation, kept local as the principles ask, but R2's `stepLeader` must get it from R4's
  tracker (the `Voters` maps); request a law from R4 in `req/go_etcd_io_raft_v3_quorum.md` (or say
  where the bound comes from), else L16 has an unsourced premise like F3.
- **S4. `ReqStart`'s `Assumes:`** says validate makes `MaxCommittedSizePerReady` non-zero; it does
  only if `MaxSizePerMsg ≠ 0` (raft.go:319-321). The premise's real source is `ConfigOk`
  (`issues/raft-zero-max-size-per-msg.md`); say so.
- **S5. Snippets that re-read below the floor**: `ReqConflictHint` re-reads `term(j)` for `hint < j ≤
  index` and panics on any error, and `ReqCompactApplied` panics on `term(i+1) == ErrCompacted`; with
  the concurrent compaction the specs (rightly) admit, both can see `ErrCompacted` when `j` (or
  `i+1`) is below `compactFloor`. Add `index ≥ compactFloor` / "no other compaction" to their
  `Assumes:` (the callers do not re-read, so this is the snippet's, not the spec's, problem).
- **S6. Patterns only listed, not exercised**: L4 (`handleHeartbeat`'s `commitTo(m.Commit)`: the
  pre `c ≤ lastIndex` comes from the heartbeat's `commit ≤ pr.Match` and the follower's ack; a
  one-line snippet would pin it), L8 (`committedEntryInCurrentTerm`: check `== term ⇒ termOf
  committed = some term`), L15 (`Bootstrap`: `raftLog_storageLastIndex`, `append` at 1, `committed :=
  len`), L1's `appliedTo(c.Applied, 0)` and the attach, L17 (`reset`'s fresh queue), L10's apply ack
  (`payloadsSize`, `reduceUncommittedSize`). Each spec's pre is establishable at the call site as far
  as I checked (L4 by R2's protocol invariant); the snippets are cheap.

## Call sites checked (pre establishable, post sufficient)

- appendEntry (raft.go:831-852): `k = lastIndex + 1 > committed` (Wf, and `lastIndex = end` with no
  snapshot pending), `k ≤ offset + |ents|`; wrap: F3. Post gives `li = k + |es| - 1` by the model.
- handleAppendEntries (1811-1845): `committed ≤ prev` from the early return; log-matching premise
  from `msgSent` (R2); slice: F2. Reject path: `term`'s three outcomes are exactly
  `zeroTermOnOutOfBounds`' pre.
- maybeSendAppend/maybeSendSnapshot (620-690): `Next ≥ 1` (tracker) avoids `term`'s `2^64-1` arm
  without `logCompactedLb`; then every `ErrCompacted` gives `logCompactedLb ≥ 1`, so `snapshot()`'s
  result is non-empty; its error is only `ErrSnapshotTemporarilyUnavailable`. `ErrUnavailable` at
  `Next - 1 > lastIndex` would reach the empty-snapshot panic: excluded by the leader's
  `Next ≤ lastIndex + 1` (R2/R4's invariant, Leader Completeness for the follower's `committed` acks).
- restore (1877-1945): `committed < s.index` checked; `snapshotPts` and `snapValid` from the message
  (R2's 3h request); fast-forward `commitTo(s.index)`: `matchTerm` true gives `termOf s.index = some`,
  hence `s.index ≤ lastIndex` by the model.
- hasUnappliedConfChanges (1013-1040): `compactFloor < applied + 1` needs `base ≤ applied`, true when
  no snapshot is pending, which `hup` checks first (`promotable`, 997); `hi ≤ lastIndex + 1` by Wf.
- acceptReady (425-436): `acceptApplying`'s `applied ≤ i ≤ committed` from `nextCommittedEnts`'s
  prefix of `[applying+1, maxAppliable]`; `acceptUnstable`'s `handing = false` from the previous
  `Advance`'s absorb (R1's `readyStor ... none k []`, an empty hand-out via `logPending_noEnts`).
- read index (2159-2166, 1611-1625): `heartbeatCtx` is `[]` or 8 bytes (recvAck's premise); a
  follower's echo is a context of this queue within the term (the queue is reset only on term
  change and a node leads a term at most once), so `ackOf v ≤ position`; voters non-empty
  (confchange refuses removing all voters).

## Ranking (need of revision)

1. `ApiLog.lean`'s laws: `raftLog_publish` (F1) and `logStor_read` (F5); the `LogState` ghost for F1.
2. `raftLog__maybeAppend.lean` with R2's `logSliceFromMsgApp` and 3h's `msgPts` (F2: cross-batch).
3. The `2^63` premises on `entries`/`nextCommittedEnts`/`scan`/`slice` (F3: settle with R2's bound).
4. `raftLog__stableTo.lean` / R2's `ackPre` (F4: record the bug, name the premise).
5. Snippets: add the between-`Ready`-and-`Advance` cases, the vote, and the S6 patterns; fix
   `ReqFollowerAppend`'s, `ReqConflictHint`'s, `ReqCompactApplied`'s and `ReqStart`'s `Assumes:`.
6. `readOnly__maybeAdvance.lean` (S3: source of the voter bound), `raftLog__acceptUnstable.lean`
   (S2: note only). The util.go/types.go helpers, `unstable__*` and the remaining read specs need
   nothing.

## Verdict

Not done. The log's read specs and the client-write laws are complete for the steady-state paths
and match the Go code, but two first-tier gaps are not recorded anywhere: the applied floor cannot be
published after a truncation or a newer snapshot between `Ready` and `Advance` (F1), so the `Advance`
acknowledgement R2 and R1 promise is unprovable in reachable runs; and the follower's append cannot
establish `maybeAppend`'s indexed entry slice from the message (F2). F5 is a small missing law.
F3 and F4 are the author's open questions 2 and 1; F4 also needs its record in `nonissues/`.
