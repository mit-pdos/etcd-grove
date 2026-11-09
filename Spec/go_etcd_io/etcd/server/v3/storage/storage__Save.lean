/-
## `(*storage).Save(st, ents)` (`storage.go:70-74`, `wal.go:1032-1074`): trusted (names only)

**Users.** The raft loop (2d's `raftNode.start`): each `Ready`'s hard state and entries, before it
fires the batch's `readyEnter` (R1: the durable state moves at the write) and, for a follower,
before it sends. Snippet: `etcdserverboot/storage.go` (`ReqSaveOrder`).

**Why it is true.** Under the read lock, `WAL.Save`: nothing for an empty state and no entries;
else each entry's record, the state's record, an fsync when `raft.MustSync` (a new term, vote or
entries) or a segment cut (which fsyncs). The records a restart reads are then `R.save hs k es`
(`Wal.Recs.save`): the linearization point is the write (no crash in scope: a commit-only state
not fsynced is still read back after the stop's `Close`, which fsyncs). An I/O error is returned,
and the raft loop exits (`Fatal`): `diskOk` excludes it.

**Changes** (from the WAL API's `walSave_spec`, `wal-api.md`): over the records model; the entries
with their first index (`Raft.entriesRO`).

**Margin.** The update fires once, at the write.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.Api
public import Spec.go_etcd_io.raft.v3.Api
public import Spec.go_uber_org.zap.Api

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

/-- **Writes the hard state and the entries from index `k`** to the WAL, durably. -/
def storage.Save.spec : Prop :=
  ∀ (s : Loc) (wd sd : GoString) (q : Qp) (hp : Loc) (dq : DFrac) (hs : Raft.HardState)
    (sl : GoSlice) (k : Nat) (es : List Raft.LogEntry) (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ isStorage s wd sd ∗ storageOpen s q ∗ Raft.hsPtr hp dq hs ∗
      Raft.entriesRO sl k es ∗ ⌜diskOk⌝ ∗
      (AU <{ ∃∃ (R : Wal.Recs), Wal.walRecs wd R }> @ ⊤, ∅
        <{ Wal.walRecs wd (R.save hs k es), COMM Q }>) }}
    (App (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty @!! go!"Save")) (Val #hp)) (Val #sl))
  {{ RET #GoInterface.nil; storageOpen s q ∗ Raft.hsPtr hp dq hs ∗ Q }}

end spec

end ServerStorage
end EtcdGrove
end Perennial
