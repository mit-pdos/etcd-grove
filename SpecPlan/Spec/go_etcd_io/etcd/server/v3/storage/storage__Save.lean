/-
## `(*storage).Save(st, ents)` (`storage.go:70-74`, `wal.go:1032-1074`): trusted (names only)

**Users.** The raft loop (2d's `raftNode.start`): each `Ready`'s hard state and entries, before it
fires the batch's `readyEnter` (R1: the durable state moves at the write) and, for a follower,
before it sends. Snippet: `etcdserverboot/storage.go` (`ReqSaveOrder`).

**Why it is true.** Under the read lock, `WAL.Save`: nothing for an empty state and no entries;
else each entry's record, the state's record, an fsync when `raft.MustSync` (a new term, vote or
entries) or a segment cut (which fsyncs). Two updates: the first before the first record is
written (`Wal.walWriting wd R (.save hs k es)`: a crash from then on leaves what
`Wal.Recs.crashedMid` allows, `Wal.walWriting_crash`), the second once the records are written and,
when `mustSync`, fsynced (`Wal.walRecs wd (R.save hs k es)`; a commit-only state not fsynced is
`Recs.crashed`'s). The raft loop fires the batch's `readyEnter` (R1) in the second. An I/O error is
returned, and the raft loop exits (`Fatal`): `diskOk` excludes it.

**Changes** (from the WAL API's `walSave_spec`, `wal-api.md`): over the records model; the entries
with their first index (`Raft.entriesRO`). Round 1 (provability F2): the update's premise places
the entries (above the floor, no gap), where the model is the replay's.
Changes: verify-round (A8 provability F1.2-3): two updates around the write (`walWriting`), so that
a crash during it is described (`Wal.walWriting_crash`); round 1 had one, at the write, with no
crash in scope.

**Margin.** None (the empty save, which writes nothing, fires both updates at once).
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.Api
public import SpecPlan.Spec.go_etcd_io.raft.v3.Api
public import SpecPlan.Spec.go_uber_org.zap.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ServerStorage

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.Assumptions]

/-- **Writes the hard state and the entries from index `k`** to the WAL, durably: an update as the
write begins, a second when it is done. -/
def storage.Save.spec : Prop :=
  ∀ (s : Loc) (wd sd : GoString) (q : Qp) (hp : Loc) (dq : DFrac) (hs : Raft.HardState)
    (sl : GoSlice) (k : Nat) (es : List Raft.LogEntry) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ isStorage s wd sd ∗ storageOpen s q ∗ Raft.hsPtr hp dq hs ∗
      Raft.entriesRO sl k es ∗ ⌜diskOk⌝ ∗
      (AU <{ ∃∃ (R : Wal.Recs), Wal.walRecs wd R ∗
              ⌜es = [] ∨ (R.floor < k ∧ k ≤ R.floor + R.log.length + 1)⌝ }> @ ⊤, ∅
        <{ Wal.walWriting wd R (.save hs k es), COMM
           AU <{ Wal.walWriting wd R (.save hs k es) }> @ ⊤, ∅
             <{ Wal.walRecs wd (R.save hs k es), COMM Q }> }>) }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty @!! go!"Save")) (Val #hp)) (Val #sl))
  {{ RET #GoInterface.nil; storageOpen s q ∗ Raft.hsPtr hp dq hs ∗ Q }}

end spec

end ServerStorage
end EtcdGrove
end Perennial
