/-
## `(*storage).SaveSnap(snap)` (`storage.go:55-66`, `wal.go:1076-1098`): trusted (names only)

**Users.** The raft loop (a received snapshot, before its `Save`), the apply thread's `snapshot`
(2d). Snippet: `etcdserverboot/storage.go`.

**Why it is true.** Under the read lock, a `walpb.Snapshot` of the metadata's index, term and
configuration, encoded and fsynced (`SaveSnapshot`). `ValidateSnapshotForWrite` refuses a nil
configuration, which a raft snapshot never has (`Raft.snapshotPts`: its `ConfState` is there).

Two updates, as `Save`'s: the first before the record is written (`Wal.walWriting wd R (.saveSnap
s)`: a crash then loses the record or keeps it, `Wal.Recs.crashedDuring`), the second after its
fsync.
**Changes** (from `walSaveSnap_spec`): over the records model. Verify-round (A8 provability F1.2):
two updates around the write (`walWriting`). **Margin.** None.
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

/-- **Writes a snapshot record** for the snapshot's index, term and configuration, durably. -/
def storage.SaveSnap.spec : Prop :=
  ∀ (s : Loc) (wd sd : GoString) (q : Qp) (p : Loc) (dq : DFrac) (sn : Raft.Snapshot)
    (Q : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage ∗ isStorage s wd sd ∗ storageOpen s q ∗ Raft.snapshotPts p dq sn ∗ ⌜diskOk⌝ ∗
      (AU <{ ∃∃ (R : Wal.Recs), Wal.walRecs wd R }> @ ⊤, ∅
        <{ Wal.walWriting wd R (.saveSnap ⟨sn.index, sn.term, some sn.conf⟩), COMM
           AU <{ Wal.walWriting wd R (.saveSnap ⟨sn.index, sn.term, some sn.conf⟩) }> @ ⊤, ∅
             <{ Wal.walRecs wd (R.saveSnap ⟨sn.index, sn.term, some sn.conf⟩), COMM Q }> }>) }}
    (App (Val (s @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.storage.storage.ty @!! go!"SaveSnap")) (Val #p))
  {{ RET #GoInterface.nil; storageOpen s q ∗ Raft.snapshotPts p dq sn ∗ Q }}

end spec

end ServerStorage
end EtcdGrove
end Perennial
