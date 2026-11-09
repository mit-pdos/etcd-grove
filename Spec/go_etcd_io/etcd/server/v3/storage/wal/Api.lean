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
* `walPurgeRight wd` (exclusive): **the right to purge `wd`'s unlocked files**
  (`fileutil.PurgeFileWithDoneNotify` in `EtcdServer.purgeFile`). `Close` releases every lock, so
  the records survive a close only once the purge has stopped: `Close` takes this right; the purge
  goroutine holds it while it runs and deposits it when it stops (old critique 2 of `wal-api.md`).

## Laws

`walRecs_timeless`, `walRecs_excl`, `walOpen_excl`, `walPurgeRight_excl`.

## What the model does not say

Crashes: `Save` of a commit-only hard state does not fsync (`raft.MustSync`), so after a crash the
directory may hold an older state record. The records here are those of a directory closed by
`Close` (which fsyncs); a crash rule (Perennial's crash semantics: the records' durable part, the
last fsynced prefix) is out of this batch's scope (`notes/specs-only/batch-2e.md`, open question
Q2).
-/
module

public import Spec.go_etcd_io.raft.v3.Model
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal
public import Spec.PkgInit.go_etcd_io.etcd.server.v3.storage.wal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Wal

open Iris Iris.BI

/-- A snapshot record (`walpb.Snapshot`). -/
structure WalSnap where
  index : w64
  term : w64
  conf : Option Raft.ConfState

/-- **A WAL directory's records** (see the header). `log` holds the entries of indices
`floor + 1, floor + 2, ...` as a replay reconstructs them. -/
structure Recs where
  meta : List w8
  hs : Raft.HardState
  floor : Nat
  log : List Raft.LogEntry
  snaps : List WalSnap

/-- A new WAL (`wal.Create`): the metadata, an empty state, an empty log, the zero snapshot record
(which `Create` writes). -/
def Recs.init (meta : List w8) : Recs :=
  { meta := meta, hs := Raft.HardState.empty, floor := 0, log := [],
    snaps := [⟨W64 0, W64 0, none⟩] }

/-- `Save(hs, ents)`, the entries `es` from index `k` (`k = 0`: none): the log truncated at `k`
and extended, the state record replaced when `hs` is not empty (an empty `hs` and no entries: no
write at all, `wal.go:1037`). -/
def Recs.save (R : Recs) (hs : Raft.HardState) (k : Nat) (es : List Raft.LogEntry) : Recs :=
  let R1 := if es = [] then R else { R with log := R.log.take (k - R.floor - 1) ++ es }
  if hs = Raft.HardState.empty then R1 else { R1 with hs := hs }

/-- `SaveSnapshot(s)`: the record appended. -/
def Recs.saveSnap (R : Recs) (s : WalSnap) : Recs := { R with snaps := R.snaps ++ [s] }

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

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext]

/-- **The WAL directory `wd` holds the records `R`** (exclusive; see the header). -/
opaque walRecs (wd : GoString) (R : Recs) : IProp GF := iprop(True)

/-- **`w` is an open WAL of directory `wd`** (exclusive). -/
opaque walOpen (w : Loc) (wd : GoString) : IProp GF := iprop(True)

/-- **The right to purge `wd`'s unlocked files** (exclusive). -/
opaque walPurgeRight (wd : GoString) : IProp GF := iprop(True)

def walRecs_timeless.spec : Prop := ∀ wd R, Timeless (walRecs (GF := GF) wd R)

def walRecs_excl.spec : Prop := ∀ wd R R',
  walRecs (GF := GF) wd R ∗ walRecs wd R' ⊢ iprop(False)

def walOpen_excl.spec : Prop := ∀ w w' wd,
  walOpen (GF := GF) w wd ∗ walOpen w' wd ⊢ iprop(False)

def walPurgeRight_excl.spec : Prop := ∀ wd,
  walPurgeRight (GF := GF) wd ∗ walPurgeRight wd ⊢ iprop(False)

end res

end Wal
end EtcdGrove
end Perennial
