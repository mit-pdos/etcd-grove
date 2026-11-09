/-
# Raft's log (batch R3): the vocabulary

The log (`log.go`'s `raftLog` with its embedded `unstable`, `log_unstable.go`), the read-index queue
(`read_only.go`'s `readOnly`) and `util.go`'s log helpers. Their clients are raft's core (R2,
`raft.go`) and its node API (R1: `rawnode.go`, `bootstrap.go`, `status.go`); nothing outside raft
sees them. The pure model is transparent (below); the resources are opaque; the laws are obligations
(`def <law>.spec : Prop`). The function specs are the files `raftLog__*.lean`, `unstable__*.lean`,
`readOnly__*.lean`, `newLogWithSize.lean`, ... beside this one.

## The shape, in words

**The log's state** is a `LogState`, Go-shaped: the `unstable` struct's fields (`UnstableState`:
the pending snapshot, the unstable entries from `offset`, `offsetInProgress`, `snapshotInProgress`),
`committed`, `applying`, `applied` and the applying budget, plus four ghost fields raft's Go state
does not hold:
- `base`/`baseTerm`: the index (and term) the log starts after: the storage's compaction point when
  the log was made, or the snapshot last restored;
- `stored`: **raft's knowledge of the storage's entries** after `base`: what the client wrote for it
  (each write is a batch the log handed out, absorbed back into the state by `raftLog_absorb`); the
  stable part of the log (`[base+1, offset-1]`) is read from the storage and is `stored`'s prefix;
- `snapStored`: the pending snapshot has been installed in the storage (absorbed);
- `handing`: a batch has been handed out (`acceptUnstable`) and not yet absorbed.
The functions over it (`LogState.lastIndex`, `termOf`, `log`, `range`) compute what Go computes, so
a read's spec is "returns `ls.lastIndex`", with one margin: the storage may be compacted
concurrently, up to `compactFloor` (the applied index, or the base), so a read below it may answer
`ErrCompacted` instead.

**`raftLog l ls`** (exclusive): the `raftLog` struct at `l` holds `ls`, with the storage behind it.
The struct is touched by raft's goroutine only; the storage is shared with the client, which writes
it (Ready's `Append`/`ApplySnapshot`, `Compact`, `CreateSnapshot`, `SetHardState`) concurrently with
raft's reads. So the storage's contents `S σ` live in an invariant the log allocates when the storage
is **attached** (`logFresh_attach`), and the client writes only through the log's laws:
- `logStor_install`, `logStor_append`: the batch a `Ready` handed out (`logPending l h snapLeft
  entsLeft`, from `acceptUnstable`), in order; `raftLog_absorb` then folds the written batch into
  `ls.stored`;
- `logStor_compact`: up to a floor (`logFloor l i t`: an index raft published as applied,
  `raftLog_publish`, or the stored snapshot's) and the stored snapshot (`logSnapLb l j`);
- `logStor_createSnapshot`: at a stored committed index (`logStored l i t`: given by the append for
  the batch's committed entries, by `raftLog_storedStable` for the stable ones, by any floor), of a
  valid snapshot (the client's `V s`) of its term;
- `logStor_read`: a read (the compaction point is a floor, the stored snapshot valid);
- `logStor_setHardState`: any hard state (the log does not read it).
`logStorage l S V N` (persistent) names the attached storage: its contents predicate `S` (R1's
`isStorage` contract), the validity `V` of the snapshots the storage may hold (raft's core takes
`snapValid γ`), and the invariant's namespace `N` (the laws' updates open it: their outer mask must
contain `↑N`).

**Starting.** `newLogWithSize` reads the storage while the caller still holds `S σ` (raft's
`newRaft` calls `InitialState` right after it, which needs `S σ` itself: R1's `isStorage`). The
log is then `raftLog l ls` in its starting mode: `logStarting l S σ` says the storage is not yet
attached and is at `σ`; `raftLog_borrowStarting` lends `S σ` out for `InitialState`; raft's reads
work in both modes (in the starting mode `raftLog` owns `S σ`). `logFresh_attach` moves `S σ` into
the invariant and gives `logStorage` (raft's core does it at the end of `newRaft`, after
`loadState`).

**Acknowledgements.** `stableTo(id)` and `stableSnapTo(i)` (the storage's `MsgStorageAppendResp`)
move the stable boundary; their premises (`StableOk`, `SnapAckOk`) say the log's contents do not
change: the entries made stable are those the storage holds (`stored`). The caller (R2) proves them
from what it knows of `stored` (entries the node once had, with the cluster's log matching).

**Published facts** (persistent): `logFloor l i t` (the storage may be compacted through `i`, and
its term at `i` is `t`: raft has applied through `i`, or `i` is the compaction point or the stored
snapshot's), `logSnapLb l j` (the storage holds a snapshot at `j` or
later), `logCompactedLb l j` (an index below `j` was found compacted: the snapshot the log sends,
`raftLog.snapshot()`, is at `j` or later).

**The read-index queue**: `readOnly ro rs` over `ReadOnlyState` (the option, the acknowledged
positions, the unconfirmed requests with their commit indices, the count confirmed): mirrors the
code. `maybeAdvance` takes the voters' configuration through R4's quorum (`jointConfigOwn`) and computes the joint quorum index `JointIdx`.

## Intended realization

- `raftLog l ls`: `l ↦ lv` with `lv`'s fields `ls`'s (the `unstable` field's as `unstable (l's
  unstable field) ls.us`), `lv.storage ↦□` its storage (constant), `loggerOk` of both loggers, and a
  ghost authority over `ls`'s ghost fields shared with the storage invariant; in the starting mode,
  `S σ` with `logStarting`'s token; attached, an invariant in `N`:
  `∃ σ ls', S σ ∗ ghost(ls') ∗ ⌜StorRel σ ls'⌝ ∗ (σ.snap.isEmpty ∨ □ V σ.snap) ∗ floors`, where
  `StorRel` says: unless a snapshot is pending and not stored, `σ`'s entries are `stored`'s from
  `σ.off` on (`σ.ents = stored.drop (σ.off - base)`, `base ≤ σ.off`, `σ.termAt base = baseTerm` if
  `σ.off = base`), plus the effect of the batch handed out and written but not absorbed; `σ.off` is
  at most the published floor (or the base); every floor is at most `σ.last` and at most
  `committed`, and `σ`'s term there (if not compacted) is the floor's (`ls.frozen`'s terms are the
  storage's: written committed entries, which no later write changes, since a later batch rewrites
  a committed index only with the same entry); the floor may exceed the stable index (after a
  truncation or a restore between `Ready` and `Advance`), which is harmless: raft reads the unstable
  part first, and a read below the floor may answer `ErrCompacted`. The stored snapshot's index is at most `committed` (true at the attach: `StorageHolds`; a restored
  snapshot is past `committed`). The floors are mono-nat authorities (`logFloor`'s index with the
  frozen term map, `logSnapLb`, `logCompactedLb`). `logPending` is the client's half of a ghost
  variable holding the batch handed out (its other half in the invariant, its existence recorded
  by `ls.handing`).
- `unstable u us`: the struct's fields, `entriesRO` of its entries with their slice capacity, the
  pending snapshot read-only (`snapshotPts □`: a clone nothing writes), and `loggerOk` of its
  `logger` field (persistent: `stableTo` and `truncateAndAppend` log; verify-round A5 S1).
- `readOnly ro rs`: the struct, `ownMap` of `acks`, the `unconfirmedReads` slice with each request
  `↦□` (a request is never written after `addRequest`; `maybeAdvance` hands the confirmed prefix
  out read-only, as the old spec did).

## raftpb, quorum and proto

(Integration I2: were provisional.) `entryRO p k e` (one `*Entry`, read-only, at index `k`) and
`entriesRO` are raftpb's (`RaftPb.entryRO`, `RaftPb.entriesRO`: definitions over `entryPts`,
re-exported by `Api.lean`); `ConfState.Equiv` is raftpb's; `jointConfigOwn c dq s0 s1` (a
`JointConfig` value whose halves are the voter sets `s0`, `s1`), `MajorityIdx` and `JointIdx` are
quorum's (`Quorum.*`, R4: the same bodies), re-exported here. `proto.Size` of an entry is 2a's
(`proto/Api.lean`; requested in `req/google_golang_org_protobuf_proto.md`).

## Requirement snippets

`examples/specreq/raftlog/` (`//go:build ignore`: the types are unexported): `append.go` (the
leader's append and the follower's `maybeAppend`, commit), `reads.go` (terms, slices for sends,
compaction errors leading to a snapshot), `ready.go` (the batch handed out, written, absorbed and
acknowledged; committed entries for applying), `snapshot.go` (restore, install, acknowledge),
`readindex.go` (the read-index queue), `util.go` (the helpers).
-/
module

public import Spec.go_etcd_io.raft.v3.Api
public import Spec.go_etcd_io.raft.v3.quorum.Api
public import Perennial.Std.Word.LittleEndian

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

-- **Two `ConfState`s list the same configuration** (`ConfState.Equivalent`): raftpb's.
-- Quorum's indices (`MajorityConfig.CommittedIndex`, `JointConfig.CommittedIndex`) and the Go
-- ownership of a `JointConfig`: R4's.
export RaftPb (ConfState.Equiv)
export Quorum (MajorityIdx JointIdx jointConfigOwn)

/-! ## The unstable part (`log_unstable.go`) -/

/-- **The `unstable` struct's state**: the pending snapshot (`snapshot`, `nil` as `none`), the
unstable entries (`entries`), the index of the first (`offset`), whether the snapshot is being
written (`snapshotInProgress`), and the index after the last entry being written
(`offsetInProgress`). -/
structure UnstableState where
  snap : Option Snapshot
  ents : List LogEntry
  offset : Nat
  snapInProgress : Bool
  offsetInProgress : Nat

namespace UnstableState

/-- `maybeFirstIndex`. -/
def maybeFirstIndex (us : UnstableState) : Option Nat :=
  us.snap.map (fun s => uint.nat s.index + 1)

/-- `maybeLastIndex`. -/
def maybeLastIndex (us : UnstableState) : Option Nat :=
  if us.ents ≠ [] then some (us.offset + us.ents.length - 1)
  else us.snap.map (fun s => uint.nat s.index)

/-- `maybeTerm(i)`. -/
def maybeTerm (us : UnstableState) (i : Nat) : Option w64 :=
  if i < us.offset then
    match us.snap with
    | some s => if uint.nat s.index = i then some s.term else none
    | none => none
  else
    match us.maybeLastIndex with
    | none => none
    | some last => if last < i then none else (us.ents[i - us.offset]?).map (·.term)

/-- `nextEntries`: the entries not yet in progress. -/
def nextEntries (us : UnstableState) : List LogEntry :=
  us.ents.drop (us.offsetInProgress - us.offset)

/-- `nextSnapshot`: the snapshot, if not in progress. -/
def nextSnapshot (us : UnstableState) : Option Snapshot :=
  if us.snapInProgress then none else us.snap

/-- `acceptInProgress`. -/
def acceptInProgress (us : UnstableState) : UnstableState :=
  { us with
    offsetInProgress := if us.ents = [] then us.offsetInProgress else us.offset + us.ents.length,
    snapInProgress := us.snap.isSome || us.snapInProgress }

/-- `stableTo(id)`: the entries through `id` dropped, if `id` is an unstable entry of its term. -/
def stableTo (us : UnstableState) (index : Nat) (term : w64) : UnstableState :=
  if us.maybeTerm index = some term ∧ us.offset ≤ index then
    { us with ents := us.ents.drop (index + 1 - us.offset), offset := index + 1,
              offsetInProgress := max us.offsetInProgress (index + 1) }
  else us

/-- `stableSnapTo(i)`: the snapshot dropped if it is at `i`. -/
def stableSnapTo (us : UnstableState) (i : Nat) : UnstableState :=
  match us.snap with
  | some s => if uint.nat s.index = i then { us with snap := none, snapInProgress := false } else us
  | none => us

/-- `restore(s)`. -/
def restore (_us : UnstableState) (s : Snapshot) : UnstableState :=
  ⟨some s, [], uint.nat s.index + 1, false, uint.nat s.index + 1⟩

/-- `truncateAndAppend(es)`, `es` at indices `k, k+1, ...`. -/
def truncateAndAppend (us : UnstableState) (k : Nat) (es : List LogEntry) : UnstableState :=
  if k = us.offset + us.ents.length then { us with ents := us.ents ++ es }
  else if k ≤ us.offset then { us with ents := es, offset := k, offsetInProgress := k }
  else { us with ents := us.ents.take (k - us.offset) ++ es,
                 offsetInProgress := min us.offsetInProgress k }

/-- What the struct's methods need of its fields (none panics on an index, `stableTo`'s `int`
conversion stays small): `offset ≤ offsetInProgress ≤ offset + |ents|`, a pending snapshot below
`offset`, everything below `2^64`. -/
def Wf (us : UnstableState) : Prop :=
  1 ≤ us.offset ∧ us.offset ≤ us.offsetInProgress ∧
  us.offsetInProgress ≤ us.offset + us.ents.length ∧
  us.offset + us.ents.length < 2 ^ 64 ∧
  (∀ s, us.snap = some s → uint.nat s.index < us.offset) ∧
  (us.snapInProgress = true → us.snap.isSome)

end UnstableState

/-! ## The log (`log.go`) -/

/-- **A batch handed out** by `acceptUnstable` (a `Ready`'s storage writes): the snapshot to
install (if any), the entries to append, the first at index `start`, and (ghost) the log's
`committed` at the hand-out (the entries up to it are the committed log's). -/
structure Handout where
  snap : Option Snapshot
  start : Nat
  ents : List LogEntry
  upto : Nat

/-- **A `raftLog`'s state**: the `unstable` struct's, `committed`, `applying`, `applied`, the
applying budget (`applyingEntsSize`, `maxApplyingEntsSize`, `applyingEntsPaused`), and the ghost
fields (the module header): the base, raft's knowledge of the stored entries, whether the pending
snapshot is stored, whether a batch is handed out, and the **frozen terms** (`frozen j = some t`:
the storage holds a committed entry of term `t` at `j`, unless compacted or replaced by a later
snapshot; what `raftLog_publish` publishes from when the log moved since the write), and the
**published floor** (`floor`: the highest index `raftLog_publish` published, at most `applying`;
above `applied` only while `Advance` steps its acknowledgements: verify-round A4 P3, R2's
`coreIdle`). -/
structure LogState where
  us : UnstableState
  committed : Nat
  applying : Nat
  applied : Nat
  applyingSize : w64
  maxApplyingSize : w64
  applyingPaused : Bool
  base : Nat
  baseTerm : w64
  stored : List LogEntry
  snapStored : Bool
  handing : Bool
  frozen : Nat → Option w64
  floor : Nat

namespace LogState

/-- The stable index (`unstable.offset - 1`). -/
def stable (ls : LogState) : Nat := ls.us.offset - 1

/-- The index of the log's last entry, as its contents say (`unstable`'s end). -/
def «end» (ls : LogState) : Nat := ls.us.offset - 1 + ls.us.ents.length

/-- `lastIndex()` (Go: the unstable part's, else the storage's). It is `end` except in the one state
an acknowledgement passes through: a snapshot pending, every entry after it made stable. -/
def lastIndex (ls : LogState) : Nat :=
  match ls.us.maybeLastIndex with
  | some i => i
  | none => ls.base + ls.stored.length

/-- `firstIndex()` without a concurrent compaction (the storage's may be higher, up to
`compactFloor + 1`). -/
def firstIdx (ls : LogState) : Nat :=
  match ls.us.maybeFirstIndex with
  | some i => i
  | none => ls.base + 1

/-- **The index the storage may have been compacted to**: the applied index, the published floor
(above the applied index while `Advance` steps the apply acknowledgement), or the base. -/
def compactFloor (ls : LogState) : Nat := max ls.base (max ls.applied ls.floor)

/-- **The log's entries** from index `base + 1`: the stable ones (the storage's, as `stored` knows
them) then the unstable ones. -/
def log (ls : LogState) : List LogEntry :=
  ls.stored.take (ls.stable - ls.base) ++ ls.us.ents

/-- The entries at indices `[lo, hi)`. -/
def range (ls : LogState) (lo hi : Nat) : List LogEntry :=
  (ls.log.drop (lo - ls.base - 1)).take (hi - lo)

/-- **`term(i)`, as Go computes it** when the storage is not compacted past `i`: the unstable
part's answer, else `none` outside `[firstIndex - 1, lastIndex]`, else the storage's (the base's
term, or a stored entry's). -/
def termOf (ls : LogState) (i : Nat) : Option w64 :=
  match ls.us.maybeTerm i with
  | some t => some t
  | none =>
    if i + 1 < ls.firstIdx ∨ ls.lastIndex < i then none
    else if i = ls.base then some ls.baseTerm
    else (ls.stored[i - ls.base - 1]?).map (·.term)

/-- `maxAppliableIndex(allowUnstable)`. -/
def maxAppliable (ls : LogState) (allowUnstable : Bool) : Nat :=
  if allowUnstable then ls.committed else min ls.committed ls.stable

/-- `newLogWithSize` over a storage at `σ`. -/
def init (σ : StorState) (maxSize : w64) : LogState :=
  ⟨⟨none, [], σ.last + 1, false, σ.last + 1⟩, σ.off, σ.off, σ.off, W64 0, maxSize, false,
    σ.off, σ.offTerm, σ.ents, false, false, (fun j => if j = σ.off then some σ.offTerm else none),
    σ.off⟩

/-- `append(es)` (`truncateAndAppend`), `es` at `k, k+1, ...`. -/
def truncateAppend (ls : LogState) (k : Nat) (es : List LogEntry) : LogState :=
  if es = [] then ls else { ls with us := ls.us.truncateAndAppend k es }

/-- **`findConflict(es)`, `es` at `k, k+1, ...`**: the position in `es` of the first entry whose
term the log does not have at its index (a conflict, or a new entry), if any. -/
def conflict (ls : LogState) (k : Nat) (es : List LogEntry) : Option Nat :=
  (List.range es.length).find? (fun j => !decide (ls.termOf (k + j) = (es[j]?).map (·.term)))

/-- `maybeAppend`'s effect when `prev` matches: the entries from the first conflicting (or new)
one appended, then `committed` moved to `min c (prev + |es|)` (if higher). -/
def appendFrom (ls : LogState) (prev : Nat) (es : List LogEntry) (c : Nat) : LogState :=
  let ls1 := match ls.conflict (prev + 1) es with
    | none => ls
    | some j => ls.truncateAppend (prev + 1 + j) (es.drop j)
  { ls1 with committed := max ls1.committed (min c (prev + es.length)) }

/-- `stableTo(id)`. -/
def stableTo (ls : LogState) (index : Nat) (term : w64) : LogState :=
  { ls with us := ls.us.stableTo index term }

/-- `stableSnapTo(i)`: the snapshot dropped (and with it the ghost `snapStored`). -/
def stableSnapTo (ls : LogState) (i : Nat) : LogState :=
  let us' := ls.us.stableSnapTo i
  { ls with us := us', snapStored := ls.snapStored && us'.snap.isSome }

/-- The terms of the stored, committed entries `[base, min stable committed]` added to `frozen`
(when the storage is read for them: no snapshot pending unstored). -/
def freezeStable (ls : LogState) : Nat → Option w64 := fun j =>
  match ls.frozen j with
  | some t => some t
  | none =>
    if (ls.us.snap = none ∨ ls.snapStored = true) ∧ ls.base ≤ j ∧ j ≤ ls.stable ∧ j ≤ ls.committed
    then ls.termOf j else none

/-- `restore(s)`: the log restarts at the snapshot, committed at it; nothing stored after it (the
terms frozen so far are kept: the storage still holds them until the snapshot is installed). -/
def restore (ls : LogState) (s : Snapshot) : LogState :=
  { ls with us := ls.us.restore s, committed := uint.nat s.index, base := uint.nat s.index,
            baseTerm := s.term, stored := [], snapStored := false, frozen := ls.freezeStable }

/-- **The batch `acceptUnstable` hands out**: the snapshot if not yet in progress, and the unstable
entries not yet in progress. -/
def handout (ls : LogState) : Handout :=
  ⟨ls.us.nextSnapshot, ls.us.offsetInProgress, ls.us.nextEntries, ls.committed⟩

/-- `acceptUnstable()`. -/
def acceptUnstable (ls : LogState) : LogState :=
  { ls with us := ls.us.acceptInProgress, handing := true }

/-- **The written batch folded into the log's knowledge** (`raftLog_absorb`): a snapshot of the
pending one's index makes it stored (and the stored entries empty), and its index frozen; the
entries replace the stored ones from their first index (unless a later `restore` moved the base
past them: then the storage will be replaced, and they are dropped); each written entry that was
committed at the hand-out, or is committed now and is the log's, is frozen. -/
def absorb (ls : LogState) (h : Handout) : LogState :=
  let ls1 := match h.snap with
    | some s =>
      if ls.us.snap.map (fun s0 : Snapshot => s0.index) = some s.index then
        { ls with snapStored := true, stored := [],
                  frozen := fun j => if j = uint.nat s.index then some s.term else ls.frozen j }
      else ls
    | none => ls
  let fz : Nat → Option w64 := fun j =>
    match h.ents[j - h.start]? with
    | some e =>
      if h.start ≤ j ∧ (j ≤ h.upto ∨
          (j ≤ ls1.committed ∧ ls1.base < j ∧ ls1.log[j - ls1.base - 1]? = some e))
      then some e.term else ls1.frozen j
    | none => ls1.frozen j
  { ls1 with
    stored := if h.ents = [] ∨ h.start ≤ ls1.base then ls1.stored
              else ls1.stored.take (h.start - ls1.base - 1) ++ h.ents,
    frozen := fz,
    handing := false }

/-- `appliedTo(i, size)`. -/
def appliedTo (ls : LogState) (i : Nat) (size : w64) : LogState :=
  let sz := if uint.nat size < uint.nat ls.applyingSize then ls.applyingSize - size else W64 0
  { ls with applied := i, applying := max ls.applying i, applyingSize := sz,
            applyingPaused := decide (uint.nat ls.maxApplyingSize ≤ uint.nat sz) }

/-- `acceptApplying(i, size, allowUnstable)` (the size added with Go's wrap-around). -/
def acceptApplying (ls : LogState) (i : Nat) (size : w64) (allowUnstable : Bool) : LogState :=
  let sz := ls.applyingSize + size
  { ls with applying := i, applyingSize := sz,
            applyingPaused := decide (uint.nat ls.maxApplyingSize ≤ uint.nat sz ∨
              i < ls.maxAppliable allowUnstable) }

/-- **What holds of every log state** (`raftLog_wf`): the unstable struct's facts, its offset past
the base and the stored entries reaching the stable index; the pending snapshot is the base;
`applied ≤ applying ≤ committed`, `base ≤ committed ≤ end`; the storage's end is the stable
index when nothing is unstable or pending; an unpaused budget has room; with no batch out, the
storage holds the log's entries through the in-progress offset (the batches written were the
log's, and a truncation lowers the offset). -/
def Wf (ls : LogState) : Prop :=
  ls.us.Wf ∧ ls.base < ls.us.offset ∧ ls.stable - ls.base ≤ ls.stored.length ∧
  (∀ s, ls.us.snap = some s → uint.nat s.index = ls.base ∧ s.term = ls.baseTerm) ∧
  (ls.snapStored = true → ls.us.snap.isSome) ∧
  ls.applied ≤ ls.applying ∧ ls.applying ≤ ls.committed ∧ ls.base ≤ ls.committed ∧
  ls.floor ≤ ls.applying ∧
  ls.committed ≤ ls.end ∧ ls.base + ls.stored.length < 2 ^ 64 ∧
  (ls.us.ents = [] → ls.us.snap = none → ls.base + ls.stored.length = ls.stable) ∧
  (ls.applyingPaused = false → uint.nat ls.applyingSize < uint.nat ls.maxApplyingSize) ∧
  (ls.handing = false →
    ls.us.offsetInProgress - 1 ≤ ls.base + ls.stored.length ∧
    ls.stored.take (ls.us.offsetInProgress - 1 - ls.base) =
      ls.log.take (ls.us.offsetInProgress - 1 - ls.base))

/-- **`stableTo(id)` is safe** (its premise): no batch is out (the written one was absorbed: the
storage is what `stored` says), the log's contents do not change (the entries made stable are those
stored), and the storage ends where the log does once nothing is unstable. For a matching
acknowledgement the caller (R2) discharges the second from `Wf`'s in-progress agreement and the
cluster's log matching: an entry of the same index and term as the one written is the same entry,
and so is every entry before it. (A `restore` between the hand-out and the acknowledgement cannot
make a stale acknowledgement match with honest peers: `restore` runs only when the snapshot's id is
not in the log, and by log matching no leader then re-sends the handed-out id; batch-R3.md, round 1,
on the suspected gap.) -/
def StableOk (ls : LogState) (index : Nat) (term : w64) : Prop :=
  let ls' := ls.stableTo index term
  ls.handing = false ∧ ls'.log = ls.log ∧ (ls'.us.ents = [] → ls'.us.snap = none → ls'.base + ls'.stored.length = ls'.stable)

/-- **`stableSnapTo(i)` is safe**: a pending snapshot at `i` is stored, and the storage ends where
the log does once nothing is unstable. -/
def SnapAckOk (ls : LogState) (i : Nat) : Prop :=
  ls.handing = false ∧ ∀ s, ls.us.snap = some s → uint.nat s.index = i →
    ls.snapStored = true ∧ (ls.us.ents = [] → ls.base + ls.stored.length = ls.stable)

end LogState

/-! ## The read-index queue (`read_only.go`) -/

/-- **A `readOnly`'s state**: the option, the highest position each node acknowledged (`acks`),
the unconfirmed requests (`unconfirmedReads`: the `*readIndexRequest` pointers, each holding its
request message pointer and commit index), and the count confirmed (`confirmedReads`). -/
structure ReadOnlyState where
  option : w64
  acks : GMap w64 w64
  pending : List (Loc × Loc × w64)
  confirmed : w64

namespace ReadOnlyState

/-- The position of the last unconfirmed request (`heartbeatCtx`'s). -/
def position (rs : ReadOnlyState) : Nat := uint.nat rs.confirmed + rs.pending.length

/-- `recvAck(from, ctx)`. -/
def recvAck (rs : ReadOnlyState) (src : w64) (ctx : List w8) : ReadOnlyState :=
  if ctx = [] then rs
  else
    let v := leToU64 (ctx.take 8)
    let old := (rs.acks !! src).getD (W64 0)
    { rs with acks := <[src := if uint.nat old < uint.nat v then v else old]> rs.acks }

/-- The acknowledged position of `v` (`0` if none). -/
def ackOf (rs : ReadOnlyState) (v : w64) : w64 := (rs.acks !! v).getD (W64 0)

end ReadOnlyState

/-- The confirmed prefix `maybeAdvance` returns at joint index `N`, and the state after. -/
def ReadOnlyState.advance (rs : ReadOnlyState) (N : w64) : ReadOnlyState × List (Loc × Loc × w64) :=
  if uint.nat N ≤ uint.nat rs.confirmed then (rs, [])
  else
    let k := uint.nat N - uint.nat rs.confirmed
    ({ rs with pending := rs.pending.drop k, confirmed := N }, rs.pending.take k)

section vocab
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
  [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ## The log -/

/-- **The `raftLog` at `l` holds `ls`**, with its storage (in the starting mode, owned; attached,
in the log's invariant). Exclusive. -/
opaque raftLog [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (l : Loc) (ls : LogState) : IProp GF := iprop(True)

/-- **The log at `l` is starting**: its storage `S` is not attached yet and holds `σ` (constant
while starting: no one else writes it). Exclusive. -/
opaque logStarting [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (l : Loc) (S : StorState → IProp GF) (σ : StorState) : IProp GF := iprop(True)

/-- **The log at `l` reads the attached storage `S`**, whose snapshots are valid by `V`, through
its invariant in `N`. Persistent. -/
opaque logStorage [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (l : Loc) (S : StorState → IProp GF) (V : Snapshot → IProp GF) (N : Namespace) :
    IProp GF := iprop(True)

/-- **The batch `h` handed out, its writes left**: the snapshot install (`snapLeft`), then the
append (`entsLeft`). Exclusive; `acceptUnstable` gives it, `raftLog_absorb` takes it back done. -/
opaque logPending [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (l : Loc) (h : Handout) (snapLeft entsLeft : Bool) : IProp GF := iprop(True)

/-- **The storage may be compacted through `i`, and its term at `i` is `t`** (fixed while `i` is
not compacted): raft has applied through `i` (`raftLog_publish`), or `i` is the stored snapshot's
or the compaction point. Persistent. -/
opaque logFloor [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (l : Loc) (i : Nat) (t : w64) : IProp GF := iprop(True)

/-- **The storage holds a snapshot at `j` or later.** Persistent. -/
opaque logSnapLb [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (l : Loc) (j : Nat) : IProp GF := iprop(True)

/-- **The storage holds a committed entry of term `t` at `i`**, fixed (a later write rewrites a
committed index only with the same entry; a compaction or a later snapshot may cover it): what
storing a snapshot at `i` needs (`logStor_createSnapshot`), without permitting a compaction through
`i`. (Verify-round, A4 completeness F1.) Persistent. -/
opaque logStored [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (l : Loc) (i : Nat) (t : w64) : IProp GF := iprop(True)

/-- **An index below `j` was found compacted**: the snapshot the log would send
(`raftLog.snapshot()`) is at `j` or later. Persistent. -/
opaque logCompactedLb [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (l : Loc) (j : Nat) : IProp GF := iprop(True)

/-- **The `unstable` struct at `u` holds `us`** (the embedded field of a `raftLog`; its methods'
specs mirror the code). Exclusive. -/
opaque unstable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (u : Loc) (us : UnstableState) : IProp GF := iprop(True)

/-! ## The read-index queue -/

/-- **The `readOnly` at `ro` holds `rs`.** Exclusive. -/
opaque readOnly [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ro : Loc) (rs : ReadOnlyState) : IProp GF := iprop(True)

/-- The confirmed requests a `maybeAdvance` returned (slice `sl`): each `*readIndexRequest`
read-only, holding its message pointer and commit index. Persistent. -/
def readReqsRO (sl : GoSlice) (rqs : List (Loc × Loc × w64)) : IProp GF :=
  iprop(sl ↦*□ (rqs.map (·.1)) ∗
    [∗list] q ∈ rqs, q.1 ↦□ (go_etcd_io.raft.v3.readIndexRequest.mk q.2.1 q.2.2))

end vocab

/-! ## Laws -/

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
  {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
  [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Persistence of the published facts and the attachment (`entryRO`'s is raftpb's,
`RaftPb.raftpb_persistent`). -/
def logPersistent.spec : Prop :=
  (∀ l S V N, Persistent (logStorage (GF := GF) l S V N)) ∧
  (∀ l i t, Persistent (logFloor (GF := GF) l i t)) ∧
  (∀ l i t, Persistent (logStored (GF := GF) l i t)) ∧
  (∀ l j, Persistent (logSnapLb (GF := GF) l j)) ∧
  (∀ l j, Persistent (logCompactedLb (GF := GF) l j))

/-- Lower bounds weaken. -/
def logLbs_mono.spec : Prop :=
  (∀ l (i j : Nat), j ≤ i → logSnapLb (GF := GF) l i ⊢ logSnapLb l j) ∧
  (∀ l (i j : Nat), j ≤ i → logCompactedLb (GF := GF) l i ⊢ logCompactedLb l j)

/-- **What every log state satisfies.** -/
def raftLog_wf.spec : Prop :=
  ∀ l ls, raftLog (GF := GF) l ls ⊢ raftLog l ls ∗ ⌜ls.Wf⌝

/-- **The fields raft's core reads and writes directly** (`r.raftLog.committed`, `.applied`,
`.maxApplyingEntsSize`, `.storage`): readable as they are; `committed` writable to a value in
`[committed, end]` (`loadState`, `Bootstrap`). -/
def raftLog_fields.spec : Prop :=
  ∀ l ls, raftLog (GF := GF) l ls ⊢
    (∃ st : GoInterface, l.[go_etcd_io.raft.v3.raftLog, go!"storage"] ↦□ st) ∗
    l.[go_etcd_io.raft.v3.raftLog, go!"committed"] ↦ W64 ls.committed ∗
    l.[go_etcd_io.raft.v3.raftLog, go!"applied"] ↦ W64 ls.applied ∗
    l.[go_etcd_io.raft.v3.raftLog, go!"maxApplyingEntsSize"] ↦ ls.maxApplyingSize ∗
    (∀ c : Nat, l.[go_etcd_io.raft.v3.raftLog, go!"committed"] ↦ W64 c ∗
      l.[go_etcd_io.raft.v3.raftLog, go!"applied"] ↦ W64 ls.applied ∗
      l.[go_etcd_io.raft.v3.raftLog, go!"maxApplyingEntsSize"] ↦ ls.maxApplyingSize ∗
      ⌜ls.committed ≤ c ∧ c ≤ ls.end⌝ ==∗ raftLog l { ls with committed := c })

/-- **The storage's `LastIndex`, called through the log's `storage` field** (`Bootstrap`'s check
that the storage is empty): the storage's last index as the log knows it. -/
def raftLog_storageLastIndex.spec : Prop :=
  ∀ l ls (st : GoInterface) (i : GoInterfaceOk), st = interface.ok i →
    (ls.us.snap = none ∨ ls.snapStored = true) → ls.handing = false →
    {{ raftLog (GF := GF) l ls ∗ l.[go_etcd_io.raft.v3.raftLog, go!"storage"] ↦□ st }}
      (App (Val #(methods i.ty go!"LastIndex" i.v)) (Val #()))
    {{ RET (PairV #(W64 (ls.base + ls.stored.length)) #interface.nil); raftLog l ls }}

/-- **Lend the starting storage** (for `InitialState`, which needs `S σ` itself). -/
def raftLog_borrowStarting.spec : Prop :=
  ∀ l ls S σ, raftLog (GF := GF) l ls ∗ logStarting l S σ ⊢
    S σ ∗ (S σ -∗ raftLog l ls ∗ logStarting l S σ)

/-- **Attach the storage**: its contents go into the log's invariant in `N`, with the validity `V`
of the snapshots it may hold. The stored snapshot is at most `committed` (after `loadState`:
`StorageHolds`) and valid. -/
def logFresh_attach.spec : Prop :=
  ∀ l ls S σ (V : Snapshot → IProp GF) (N : Namespace) (E : CoPset),
    (∀ s, Persistent (V s)) →
    uint.nat σ.snap.index ≤ ls.committed →
    raftLog (GF := GF) l ls ∗ logStarting l S σ ∗ (⌜σ.snap.isEmpty⌝ ∨ V σ.snap) ⊢ |={E}=>
      raftLog l ls ∗ logStorage l S V N ∗ logSnapLb l (uint.nat σ.snap.index) ∗
      logFloor l σ.off σ.offTerm

/-- **Absorb a written batch** into the log's knowledge of the storage. -/
def raftLog_absorb.spec : Prop :=
  ∀ l ls h, raftLog (GF := GF) l ls ∗ logPending l h false false ⊢ |==> raftLog l (ls.absorb h)

/-- **Publish an index being applied** whose stored term is known: frozen (written and committed,
or stored and committed when a snapshot was restored), or in the stable part with nothing pending
unstored. (Verify-round, A4 P3: at `i ≤ applying` with the written batch absorbed, so that R2's
`rawNodeAt_advance` publishes the delivered log at `Advance`'s rendezvous, before the apply
acknowledgement moves `applied`: `node.Advance` returns then. The floor is recorded, `floor`: reads
until `applied` catches up may answer `ErrCompacted` up to it, `compactFloor`.) -/
def raftLog_publish.spec : Prop :=
  ∀ l ls (i : Nat) (t : w64),
    i ≤ ls.applying → ls.handing = false → ls.freezeStable i = some t →
    raftLog (GF := GF) l ls ⊢ |==> raftLog l { ls with floor := max ls.floor i } ∗ logFloor l i t

/-- **The stable committed entries are stored**: each index whose term `freezeStable` knows is held
by the storage at that term (R1's `storedLb` for the entries a `Ready` delivers that an earlier batch
wrote; R2 takes it at the hand-out). -/
def raftLog_storedStable.spec : Prop :=
  ∀ l ls, raftLog (GF := GF) l ls ⊢ |==> raftLog l ls ∗
    □ ∀ (j : Nat) (t : w64), ⌜ls.freezeStable j = some t⌝ -∗ logStored l j t

/-- A floor is stored. -/
def logFloor_stored.spec : Prop :=
  ∀ l (i : Nat) (t : w64), logFloor (GF := GF) l i t ⊢ logStored l i t

/-- **Floors agree** on the term (every floor is a committed entry's, or the compaction point's,
which the storage keeps). -/
def logFloor_agree.spec : Prop :=
  ∀ l (i : Nat) (t t' : w64), logFloor (GF := GF) l i t ∗ logFloor l i t' ⊢ ⌜t = t'⌝

/-! ### The client's storage writes -/

/-- **Install the batch's snapshot.** -/
def logStor_install.spec : Prop :=
  ∀ l S V N h (s : Snapshot) (e : Bool) (Eo : CoPset), ↑N ⊆ Eo → h.snap = some s →
    logStorage (GF := GF) l S V N ∗ logPending l h true e ⊢
      AU <{ ∃∃ σ, S σ ∗ ⌜σ.applySnapshotErr s = false⌝ }> @ Eo, ∅
        <{ S (σ.applySnapshot s), COMM logPending l h false e ∗ logSnapLb l (uint.nat s.index) ∗
             logFloor l (uint.nat s.index) s.term }>

/-- **Append the batch's entries** (after its snapshot): no gap. The batch's entries committed at
the hand-out are then stored (verify-round, A4 completeness F1). -/
def logStor_append.spec : Prop :=
  ∀ l S V N h (e : Bool) (Eo : CoPset), ↑N ⊆ Eo →
    logStorage (GF := GF) l S V N ∗ logPending l h false e ⊢
      AU <{ ∃∃ σ, S σ ∗ ⌜(σ.append h.start h.ents).isSome ∧ h.start + h.ents.length < 2 ^ 64⌝ }>
          @ Eo, ∅
        <{ S ((σ.append h.start h.ents).getD σ), COMM logPending l h false false ∗
             □ ∀ (j : Nat) (en : LogEntry), ⌜h.start ≤ j ∧ j ≤ h.upto ∧ h.ents[j - h.start]? = some en⌝ -∗
               logStored l j en.term }>

/-- A batch with no entries needs no append. -/
def logPending_noEnts.spec : Prop :=
  ∀ l (h : Handout) (e : Bool), h.ents = [] →
    logPending (GF := GF) l h false e ⊢ logPending l h false false

/-- **Compact** up to a published applied index and the stored snapshot. -/
def logStor_compact.spec : Prop :=
  ∀ l S V N (i j : Nat) (t : w64) (Eo : CoPset), ↑N ⊆ Eo → i ≤ j →
    logStorage (GF := GF) l S V N ∗ logFloor l j t ∗ logSnapLb l i ⊢
      AU <{ ∃∃ σ, S σ ∗ ⌜i ≤ σ.last ∧ i ≤ uint.nat σ.snap.index⌝ }> @ Eo, ∅
        <{ S (σ.compact i), COMM True }>

/-- **Store a valid snapshot** at a stored committed index, of its term. (Verify-round, A4
completeness F1: was at a published floor, `logFloor`, which `logFloor_stored` still gives.) -/
def logStor_createSnapshot.spec : Prop :=
  ∀ l S V N (s : Snapshot) (t : w64) (Eo : CoPset), ↑N ⊆ Eo → s.term = t →
    logStorage (GF := GF) l S V N ∗ logStored l (uint.nat s.index) t ∗ V s ⊢
      AU <{ ∃∃ σ, S σ ∗ ⌜uint.nat s.index ≤ σ.last ∧ σ.off ≤ uint.nat σ.snap.index ∧
              (σ.off ≤ uint.nat s.index → σ.termAt (uint.nat s.index) = some t)⌝ }> @ Eo, ∅
        <{ S (σ.createSnapshot (uint.nat s.index) (some s.conf) s.data),
           COMM logSnapLb l (uint.nat s.index) }>

/-- **Read the storage**: its compaction point is at most its snapshot's index and is a floor, its
snapshot empty or valid and at least any known lower bound (which it raises). -/
def logStor_read.spec : Prop :=
  ∀ l S V N (j : Nat) (Eo : CoPset), ↑N ⊆ Eo →
    logStorage (GF := GF) l S V N ∗ logSnapLb l j ⊢
      AU <{ ∃∃ σ, S σ ∗ ⌜σ.off ≤ uint.nat σ.snap.index ∧ j ≤ uint.nat σ.snap.index⌝ ∗
              logFloor l σ.off σ.offTerm ∗ (⌜σ.snap.isEmpty⌝ ∨ V σ.snap) }> @ Eo, ∅
        <{ S σ, COMM logSnapLb l (uint.nat σ.snap.index) }>

/-- **Store a hard state** (the log does not read it). -/
def logStor_setHardState.spec : Prop :=
  ∀ l S V N (hs : HardState) (Eo : CoPset), ↑N ⊆ Eo →
    logStorage (GF := GF) l S V N ⊢
      AU <{ ∃∃ σ, S σ }> @ Eo, ∅ <{ S (σ.setHardState hs), COMM True }>

/-! ### The read-index queue -/

/-- The option field, read by raft's core (`r.readOnly.option`): constant. -/
def readOnly_option.spec : Prop :=
  ∀ ro rs, readOnly (GF := GF) ro rs ⊢
    readOnly ro rs ∗ ro.[go_etcd_io.raft.v3.readOnly, go!"option"] ↦□ rs.option

end laws

end Raft
end EtcdGrove
end Perennial
