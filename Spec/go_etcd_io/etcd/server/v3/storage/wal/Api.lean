/-
# etcd's write-ahead log (`server/storage/wal`): the trust boundary's vocabulary (batch 2e)

The WAL is translated names only: no translated code calls a `wal.*` function directly. The server
reaches it through `serverstorage.Storage` (`Spec/go_etcd_io/etcd/server/v3/storage/Api.lean`: the
raft loop's `Save`, `SaveSnap`, `Release`, `Sync`, `Close`) and through `bootstrap`'s trusted
contract (`wal.Create`, `Open`, `ReadAll`, `ValidSnapshotEntries`, `Repair`). This module is the
model those statements share: **what a WAL directory holds**, as a restart reads it. It is trusted
in the sense of the old `WalRecs.lean` (`.claude/skills/spec/examples/wal-api.md`, approved): the
meaning of `walRecs` is "what a later `Open` + `ReadAll` of the directory returns", which no proof
here can check.

## The model (transparent)

* `WalSnap`: a snapshot record (`walpb.Snapshot`: index, term, the configuration it was saved with).
* `Recs`: a directory's records: the metadata (`etcdserverpb.Metadata`'s bytes: node and cluster
  id), the last hard-state record, the log as a replay from the start reconstructs it (each saved
  batch of entries from index `k` truncates the log at `k`), the snapshot records in the order
  written, and the **floor**: the index below which records may have been purged (raised by
  `release`, which the purge then makes true).
* `Recs.save`, `Recs.saveSnap`, `Recs.release`: the effect of `WAL.Save`, `SaveSnapshot`,
  `ReleaseLockTo` on the records.
* `Recs.validSnaps`, `Recs.newest`: what `ValidSnapshotEntries` and `bootstrap`'s
  `newestSnapshotEntry` pick (the records at or below the last hard state's commit; the highest
  index, the fork's fix: `bootstrap.go:436-446`); `Recs.readable`: a restart opened at that record
  reads the whole log after it (no record above it purged).

## Resources

* `walRecs wd R` (exclusive, timeless): **the WAL directory `wd` holds the records `R`**.
  Intended realization: a ghost variable, its meaning trusted (sealed: no `import all` may update
  it, `etc/import-all.txt`'s `sealed` list in the old tree). Held by the server's invariant while a
  member runs (moved by the storage's updates), by `EtcdServer.memberDisk` while it is stopped.
* `walOpen w wd` (exclusive): `w` is an open `*wal.WAL` writing to `wd`, holding its file locks.
  Given by `bootstrap`, taken by `serverstorage.NewStorage`, consumed by `Close`.
* `walWriting wd R w` (exclusive, timeless): **a write `w` (`WalWrite`: a `Save` or a
  `SaveSnapshot`) is in progress on `wd`, whose records were `R` before it** (verify-round, A8
  provability F1.2: a crash during a write leaves states `R` alone does not describe). The raft
  loop's write moves `walRecs wd R` to it when it begins writing and on to `walRecs wd (w.apply R)`
  when it is done (`storage.Save.spec`, `storage.SaveSnap.spec`: two updates); the server's disk
  invariant holds whichever of the two is current.
* `walCreating wd md` (exclusive, timeless; third crash pass, F2-crash N2): **`wal.Create` of `wd`
  with metadata `md` is between its rename and its parent's fsync**. `Create` writes a temporary
  directory `wd.tmp` (the metadata, the zero snapshot record, fsynced by `SaveSnapshot`), renames it
  onto `wd` (`renameWAL`, `wal.go:185`) and only then fsyncs the parent directory (`:225`): in
  between, a crash may keep the rename (the WAL at `Recs.init md`) or lose it (no WAL; the next
  `Create` removes the leftover `wd.tmp`). Held by 2e's `diskState` of a new member's or a joiner's
  directory in that window (`bootstrap`'s trusted contract fires the disk's access at the rename and
  at the fsync), which becomes `walRecs wd (Recs.init md)` at the fsync.
* `walPurgeRight wd` (exclusive): **the right to purge `wd`'s unlocked files**
  (`fileutil.PurgeFileWithDoneNotify` in `EtcdServer.purgeFile`). `Close` releases every lock, so
  the records survive a close only once the purge has stopped: `Close` takes this right; the purge
  goroutine holds it while it runs and deposits it when it stops (old critique 2 of `wal-api.md`).

## Laws

`walRecs_timeless`, `walRecs_excl`, `walOpen_excl`, `walPurgeRight_excl`, `walWriting_timeless`,
`walWriting_excl`, `walWriting_recs_excl`, `walCreating_timeless`, `walCreating_excl`, and the crash
laws `walRecs_crash`, `walWriting_crash`, `walCreating_crash` (third crash pass, F2-crash N2);
the crash scope `Recs.crashScopeOk` (transparent, verify round crash pass) and its environment
premise `crashInScope` (an opaque `Prop`, second crash pass: F-server-boot F2).

## Crashes (verify-round, A8 provability F1.2-3)

`Recs.crashed`: what a crash may leave of records at rest (a commit-only state record not fsynced
may be lost: the state's commit is anything from the synced commit up). `Recs.crashedDuring R w`:
what a crash during the write `w` may leave:

* a `Save` (`Recs.crashedMid`): a prefix of its entries with the old state record, **or all of
  them with the new state record not yet fsynced** (the second case was missing: under OsFs's power
  loss a dirty byte is arbitrary, its written value included, so the whole write may reach the disk
  before the fsync; R1's `raftState_crash` allows the batch's term and vote with a commit between
  the old `wcommit` and the batch's commit (its second case; the new record's commit is the
  batch's), which is this case; the first, a prefix with the old record, is its first case: the
  old term and vote, a commit between `wcommit` and `D.commit`);
* a `SaveSnapshot`: the record lost, or kept not yet fsynced.

Each then `crashed` (the commit-only loss). **Why it is true** (trusted, as the records' meaning):
`WAL.Save` writes its entries' records, then the state's, then fsyncs when `mustSync` (a segment
cut fsyncs too); `SaveSnapshot` writes one record and fsyncs; records are appended in order, each
CRC-chained, and a restart's `ReadAll` stops at a torn tail (`io.ErrUnexpectedEOF`, then
`wal.Repair` truncates it), so what survives is a prefix of the records written. A crash that
corrupts a record behind a later surviving one (or leaves garbage passing the CRC) makes `ReadAll`
fail with `ErrCRCMismatch`, which `bootstrap` treats as fatal: excluded by `ServerStorage.diskOk`
(its docstring lists it), which the crash laws take.

**A crash inside `wal.Create`** (third crash pass, F2-crash N2): before the rename nothing is at
`wd` (no law: the directory holds no WAL); between the rename and the parent's fsync,
`walCreating_crash` gives the WAL at `Recs.init md` or none; after the fsync, `walRecs wd (Recs.init
md)` and `walRecs_crash`. **Why it is true**: the rename of a directory is one entry of the parent,
kept or lost whole by a crash (ext4, xfs), and the temporary directory's file was fsynced before it
(`SaveSnapshot`); a lost rename leaves `wd` absent (`renameWAL` removed any `wd` first) or without
`.wal` files, which `wal.Exist` reads as no WAL. `Recs.init md` meets `crashScopeOk` (no entries, the
zero snapshot record at the zero commit), so the law needs no `crashInScope`.

**The crash scope** (second crash pass, F-server-boot F2): `crashInScope` (an opaque `Prop`, like
`ServerStorage.diskOk`) is W0's environment premise "every crash of the run leaves each WAL
directory so that the next `Open` + `ReadAll` returns records meeting `Recs.crashScopeOk`". Its text
is its meaning: a statement about the run, which `walRecs`'s trusted meaning (what a restart reads)
makes checkable against each crash, and which no proof here can establish. The crash laws take it
and add `⌜R'.crashScopeOk⌝` to the records they give, so the logic sees the premise: 2e's
`disk_crash` takes it and has no out-of-scope case (round 2's `crashOutOfScope` disjunct, which no
proof could refute, is gone). True under the premise: the records the laws give are the ones the
crash left, which the premise says meet `crashScopeOk`. Not vacuous: only a run whose crash leaves
records failing `crashScopeOk` makes the premise false (the margin of `crashScopeOk`'s docstring:
also an at-rest crash of a lagging follower with two conf changes above its stored commit), and a
law applied to records that already fail it at rest (a crash can only lower the stored commit, so
they fail after it too) gives `False` exactly for such a run. A law applies only with the old
generation's `crashed`, i.e. once that generation has crashed, so the premise is never used of a
running generation's records.

**Generations.** The laws take the old generation's crash token (`crashed`, Perennial's
`CrashToken`) and give `walRecs` at the next generation's heap `⟨hG.goose_globalGS, L'⟩`, as 4c's
`boltCrash` does; `walRecs` is a trusted ghost variable whose meaning (what the directory's files
make a later `Open` + `ReadAll` return) is not over OsFs's resources, so no OsFs `crashRest` is
threaded (the closed world, `EtcdServer.dataDirFresh`: nothing else writes `wd`).
-/
module

public import Spec.go_etcd_io.raft.v3.Model
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.storage.wal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

namespace ServerStorage
/-- **The environment premise of the server's storage**: declared here, below the WAL's crash laws
that take it; its meaning (the failures it excludes) is in `storage/Api.lean`'s header and on
`ServerStorage.diskOk`'s uses there. -/
opaque diskOk : Prop
end ServerStorage

namespace Wal

open Iris Iris.BI Classical

/-- A snapshot record (`walpb.Snapshot`). -/
structure WalSnap where
  index : w64
  term : w64
  conf : Option Raft.ConfState

/-- **A WAL directory's records** (see the header). `log` holds the entries of indices
`floor + 1, floor + 2, ...` as a replay reconstructs them. -/
structure Recs where
  metadata : List w8
  hs : Raft.HardState
  floor : Nat
  log : List Raft.LogEntry
  snaps : List WalSnap
  /-- the commit of the last state record known fsynced (`raft.MustSync`'s writes, a segment cut,
  `Sync`, `Close`): what a crash cannot lose -/
  syncedCommit : w64

/-- A new WAL (`wal.Create`): the metadata, an empty state, an empty log, the zero snapshot record
(which `Create` writes). -/
def Recs.init (md : List w8) : Recs :=
  { metadata := md, hs := Raft.HardState.empty, floor := 0, log := [],
    snaps := [⟨W64 0, W64 0, none⟩], syncedCommit := W64 0 }

/-- Whether `Save(hs, es)` fsyncs (`raft.MustSync`: entries, or a new term or vote). -/
def Recs.mustSync (R : Recs) (hs : Raft.HardState) (es : List Raft.LogEntry) : Prop :=
  es ≠ [] ∨ hs.term ≠ R.hs.term ∨ hs.vote ≠ R.hs.vote

/-- `Save(hs, ents)`, the entries `es` from index `k`: the log truncated at `k` and extended, the
state record replaced when `hs` is not empty (an empty `hs` and no entries: no write at all,
`wal.go:1037`). Only meaningful at `es = [] ∨ floor < k ≤ floor + |log| + 1` (the premise of
`storage.Save.spec`: an entry at or below the floor is dropped by the replay, a gap is
`ErrSliceOutOfRange`, `wal.go:500-516`). The synced commit moves when the save fsyncs. -/
def Recs.save (R : Recs) (hs : Raft.HardState) (k : Nat) (es : List Raft.LogEntry) : Recs :=
  let R1 := if es = [] then R else { R with log := R.log.take (k - R.floor - 1) ++ es }
  let R2 := if hs = Raft.HardState.empty then R1 else { R1 with hs := hs }
  if R.mustSync hs es then { R2 with syncedCommit := R2.hs.commit } else R2

/-- `SaveSnapshot(s)`: the record appended (and fsynced). When the snapshot is above the commit of
the last state record (a received snapshot), the entries above it are dropped: the fork's
`ReadAll` drops them when it opens at this record (`wal.go:539-550`,
`nonissues/etcd-wal-stale-entries-above-snapshot.md`); a restart opens at the newest valid record,
and at an older one the entries above this record are rewritten by the later saves the newer record
needs, so the model is the replay's either way. -/
def Recs.saveSnap (R : Recs) (s : WalSnap) : Recs :=
  let R1 := { R with snaps := R.snaps ++ [s], syncedCommit := R.hs.commit }
  if uint.nat R.hs.commit < uint.nat s.index ∧ R.floor ≤ uint.nat s.index then
    { R1 with log := R.log.take (uint.nat s.index - R.floor) }
  else R1

/-- **What a crash may leave of the records `R`** (true of the WAL's code: each `Save` writes its
entries, then its state, and fsyncs only when `mustSync`; `SaveSnapshot`, a segment cut, `Sync`,
`Close` fsync): a commit-only state record not yet fsynced may be lost, so the state's commit is
anything from the synced commit up. -/
def Recs.crashed (R R' : Recs) : Prop :=
  ∃ c : w64, uint.nat R.syncedCommit ≤ uint.nat c ∧ uint.nat c ≤ uint.nat R.hs.commit ∧
    R' = { R with hs := { R.hs with commit := c }, syncedCommit := c }

/-- **What a crash during `Save(hs, es)` from `k` may leave**: some prefix of the entries written
(each record a whole one: a torn tail is repaired, `wal.Repair`) with the old state record, or all
of them with the new state record (written, not yet fsynced: the synced commit is the old one),
then `crashed`. -/
def Recs.crashedMid (R : Recs) (hs : Raft.HardState) (k : Nat) (es : List Raft.LogEntry)
    (R' : Recs) : Prop :=
  (∃ j, j ≤ es.length ∧
    Recs.crashed (if j = 0 then R else { R with log := R.log.take (k - R.floor - 1) ++ es.take j }) R') ∨
  Recs.crashed { R.save hs k es with syncedCommit := R.syncedCommit } R'

/-- **A write in progress** (`walWriting`): a `Save(hs, es)` of the entries from index `k`, or a
`SaveSnapshot(s)`. -/
inductive WalWrite where
  | save (hs : Raft.HardState) (k : Nat) (es : List Raft.LogEntry)
  | saveSnap (s : WalSnap)

/-- The records once the write is done. -/
def WalWrite.apply : WalWrite → Recs → Recs
  | .save hs k es, R => R.save hs k es
  | .saveSnap s, R => R.saveSnap s

/-- **What a crash during the write `w` on records `R` may leave** (see the header). -/
def Recs.crashedDuring (R : Recs) : WalWrite → Recs → Prop
  | .save hs k es, R' => R.crashedMid hs k es R'
  | .saveSnap s, R' => R.crashed R' ∨ Recs.crashed { R.saveSnap s with syncedCommit := R.syncedCommit } R'

/-- `ReleaseLockTo(i)`, then a purge: what is below `i` may be gone. -/
def Recs.release (R : Recs) (i : Nat) : Recs :=
  if i ≤ R.floor then R else
  { R with floor := i, log := R.log.drop (i - R.floor),
           snaps := R.snaps.filter (fun s => i ≤ uint.nat s.index) }

/-- The snapshot records a restart may open at (`ValidSnapshotEntries`): at or below the last
state's commit. -/
def Recs.validSnaps (R : Recs) : List WalSnap :=
  R.snaps.filter (fun s => uint.nat s.index ≤ uint.nat R.hs.commit)

/-- The record a restart opens at: the valid one of the highest index (the last among equals). -/
def Recs.newest (R : Recs) : Option WalSnap :=
  R.validSnaps.foldl (fun o s => match o with
    | none => some s
    | some b => if uint.nat b.index ≤ uint.nat s.index then some s else some b) none

/-- A restart reads the whole log after its snapshot record: the record is at or above the floor,
and the log is contiguous up to the last state's commit. -/
def Recs.readable (R : Recs) : Prop :=
  ∃ s, R.newest = some s ∧ R.floor ≤ uint.nat s.index ∧
    uint.nat R.hs.commit ≤ R.floor + R.log.length

/-- The entries a restart opened at record `s` reads (`ReadAll`): those after `s`'s index. -/
def Recs.entsAfter (R : Recs) (s : WalSnap) : List Raft.LogEntry :=
  R.log.drop (uint.nat s.index - R.floor)

/-- **At most one conf-change entry above the last state record's commit** in the records a
restart reads (R1's `Durable.confAboveOk` of the restart view: the entries above the commit are the
same in both). -/
def Recs.confAboveOk (R : Recs) : Prop :=
  ((R.log.zipIdx (R.floor + 1)).filter
    (fun p => uint.nat R.hs.commit < p.2 ∧ p.1.isConfChange)).length ≤ 1

/-- **The crash restarts the covered executions handle** (verify round, crash pass: R-A8 N2; the
scope the user chose, `batch-2e.md` Q2 and open question 2.8, stated over what a restart reads, so
that it has a physical meaning): the records a restart reads after the crash (a) keep at most one
conf-change entry above the commit (`confAboveOk`: a crash between the entries' records and the
state record of a batch catching up across several member changes breaks it,
`issues/raft-commit-lost-with-entries-kept.md`), and (b) hold no snapshot record above the commit
(a crash after a received snapshot's record, which `SaveSnapshot` fsyncs, and before the state
record of its batch reaches the disk: the restart ignores the record, `ValidSnapshotEntries`, and
`Recs.saveSnap`'s truncation is not the replay's then). Every other crash point is covered (R1's
`raftState_crash` covers a snapshot batch with nothing or all of it written). Outside the WAL's
records, the crash is never out of scope. W0's adequacy theorem takes "every crash leaves each
member's WAL so that `Open` + `ReadAll` returns records meeting `crashScopeOk`" as its
environment premise (`walRecs`'s trusted meaning makes it a statement about the run): `crashInScope`
below, which the crash laws take (second crash pass, F-server-boot F2). Margin: an at-rest crash of a
lagging follower whose WAL holds two conf changes above its stored commit fails (a) too, though raft
handles it (`Raft.raftState_gen` has no such premise); telling it apart needs the record order in
`Recs`. -/
def Recs.crashScopeOk (R : Recs) : Prop :=
  R.confAboveOk ∧ ∀ s ∈ R.snaps, uint.nat s.index ≤ uint.nat R.hs.commit

/-- **W0's environment premise of the crash scope** (second crash pass, F-server-boot F2; see the
header, "The crash scope"): every crash of the run leaves each WAL directory so that the next `Open`
+ `ReadAll` returns records meeting `Recs.crashScopeOk`. Opaque: its text is its meaning, a fact
about the run that the adequacy theorem of a program takes as a premise beside
`ServerStorage.diskOk`; the WAL's crash laws take it. -/
opaque crashInScope : Prop

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext]

/-- **The WAL directory `wd` holds the records `R`** (exclusive; see the header). -/
opaque walRecs [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (wd : GoString) (R : Recs) : IProp GF := iprop(True)

/-- **`w` is an open WAL of directory `wd`** (exclusive). -/
opaque walOpen [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (w : Loc) (wd : GoString) : IProp GF := iprop(True)

/-- **The write `w` is in progress on `wd`, whose records were `R`** (exclusive, timeless). -/
opaque walWriting [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (wd : GoString) (R : Recs) (w : WalWrite) : IProp GF := iprop(True)

/-- **`wal.Create` of `wd` with metadata `md` is between its rename and its parent's fsync**
(exclusive, timeless; third crash pass, F2-crash N2; see the header). -/
opaque walCreating [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (wd : GoString) (md : List w8) : IProp GF := iprop(True)

/-- **The right to purge `wd`'s unlocked files** (exclusive). -/
opaque walPurgeRight [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (wd : GoString) : IProp GF := iprop(True)

def walRecs_timeless.spec : Prop := ∀ wd R, Timeless (walRecs (GF := GF) wd R)

def walRecs_excl.spec : Prop := ∀ wd R R',
  walRecs (GF := GF) wd R ∗ walRecs wd R' ⊢ iprop(False)

def walOpen_excl.spec : Prop := ∀ w w' wd,
  walOpen (GF := GF) w wd ∗ walOpen w' wd ⊢ iprop(False)

def walPurgeRight_excl.spec : Prop := ∀ wd,
  walPurgeRight (GF := GF) wd ∗ walPurgeRight wd ⊢ iprop(False)

def walWriting_timeless.spec : Prop := ∀ wd R w, Timeless (walWriting (GF := GF) wd R w)

def walWriting_excl.spec : Prop := ∀ wd R R' w w',
  walWriting (GF := GF) wd R w ∗ walWriting wd R' w' ⊢ iprop(False)

/-- A directory is at rest or being written, not both. -/
def walWriting_recs_excl.spec : Prop := ∀ wd R R' w,
  walWriting (GF := GF) wd R w ∗ walRecs wd R' ⊢ iprop(False)

def walCreating_timeless.spec : Prop := ∀ wd md, Timeless (walCreating (GF := GF) wd md)

/-- One directory state: being created, or at rest or written. -/
def walCreating_excl.spec : Prop :=
  (∀ wd md md', walCreating (GF := GF) wd md ∗ walCreating wd md' ⊢ iprop(False)) ∧
  (∀ wd md R, walCreating (GF := GF) wd md ∗ walRecs wd R ⊢ iprop(False)) ∧
  (∀ wd md R w, walCreating (GF := GF) wd md ∗ walWriting wd R w ⊢ iprop(False))

/-- **A crash of records at rest** (trusted; see the header): the next generation `L'` finds the
records `R` with a commit-only state possibly lost, in the crash scope. Changes (second crash pass,
F-server-boot F2): takes the environment premise `crashInScope` and gives `⌜R'.crashScopeOk⌝` (true
under it: `R'` is what the crash left). -/
def walRecs_crash.spec : Prop := ∀ (L' : GooseLocalGS GF) (wd : GoString) (R : Recs),
  ServerStorage.diskOk → crashInScope →
  walRecs (GF := GF) wd R ∗ crashed ⊢
    |==> ∃ R' : Recs, ⌜R.crashed R' ∧ R'.crashScopeOk⌝ ∗
      @walRecs _ _ _ GF ⟨hG.goose_globalGS, L'⟩ wd R'

/-- **A crash during a write** (trusted; see the header): the next generation `L'` finds a state
the interrupted write may leave, in the crash scope. Changes (second crash pass, F-server-boot F2):
as `walRecs_crash`. -/
def walWriting_crash.spec : Prop := ∀ (L' : GooseLocalGS GF) (wd : GoString) (R : Recs)
    (w : WalWrite),
  ServerStorage.diskOk → crashInScope →
  walWriting (GF := GF) wd R w ∗ crashed ⊢
    |==> ∃ R' : Recs, ⌜R.crashedDuring w R' ∧ R'.crashScopeOk⌝ ∗
      @walRecs _ _ _ GF ⟨hG.goose_globalGS, L'⟩ wd R'

/-- **A crash inside `wal.Create`, between its rename and its parent's fsync** (trusted; third crash
pass, F2-crash N2; see the header, "A crash inside `wal.Create`"): the next generation `L'` finds the
new WAL (`Recs.init md`, in the crash scope) or no WAL at `wd` (nothing). -/
def walCreating_crash.spec : Prop := ∀ (L' : GooseLocalGS GF) (wd : GoString) (md : List w8),
  ServerStorage.diskOk →
  walCreating (GF := GF) wd md ∗ crashed ⊢
    |==> @walRecs _ _ _ GF ⟨hG.goose_globalGS, L'⟩ wd (Recs.init md) ∨ iprop(emp)

end res

end Wal
end EtcdGrove
end Perennial
