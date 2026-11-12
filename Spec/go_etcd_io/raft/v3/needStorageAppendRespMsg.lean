/-
`needStorageAppendRespMsg(r, rd)` (`rawnode.go:210`), Lean-first (2026-10-16, stage R5 of the
raft v3.7 retarget; the old proof stepped through it inline in `RawNode.acceptReady`'s).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `needStorageAppendRespMsg(r, rd)` is `r.raftLog.hasNextOrInProgressUnstableEnts() ||
!IsEmptySnap(rd.Snapshot)`: whether the log has unstable entries or the `Ready` hands out a snapshot
(D22 S-d3a, 2026-10-21: `rd.Snapshot` `nil` or holding a non-empty snapshot `o`, at any fraction;
until then `nil` only). Stated on what it reads of the raft struct, the `raftLog` field and the log
(`RawNode.acceptReady` holds the struct open, `ownRaftPhysReady`, so not `ownRaftPhysCV`). -/
abbrev needStorageAppendRespMsg.spec : Prop :=
  ∀ (r l : Loc) (ls : LogState) (rd : Ready) (dq : DFrac) (o : Option SnapshotM),
  (∀ sv, o = some sv → sv.Metadata'.Index' ≠ W64 0) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      r.[raft, go!"raftLog"] ↦ l ∗ ownRaftLog l ls ∗ snapOpt rd.Snapshot' dq o }}
    (App (App (Val #(functions needStorageAppendRespMsg [])) (Val #r)) (Val #rd))
  {{ RET #(decide (ls.uents ≠ []) || o.isSome);
      r.[raft, go!"raftLog"] ↦ l ∗ ownRaftLog l ls ∗ snapOpt rd.Snapshot' dq o }}

end spec

end EtcdGrove
end Perennial
