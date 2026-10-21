/-
`needStorageAppendRespMsg(r, rd)` (`rawnode.go:210`), Lean-first (2026-10-16, stage R5 of the
raft v3.7 retarget; the old proof stepped through it inline in `RawNode.acceptReady`'s).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvRawnode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `needStorageAppendRespMsg(r, rd)` is `r.raftLog.hasNextOrInProgressUnstableEnts() ||
!IsEmptySnap(rd.Snapshot)`: with no snapshot in the `Ready` (`rd.Snapshot = nil`, the node
layer's scope), whether the log has unstable entries. Stated on what it reads of the raft
struct, the `raftLog` field and the log (`RawNode.acceptReady` holds the struct open,
`ownRaftPhysReady`, so not `ownRaftPhysCV`). -/
abbrev needStorageAppendRespMsg.spec : Prop :=
  ∀ (r l : Loc) (ls : LogState) (rd : Ready),
  rd.Snapshot' = null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      r.[raft, go!"raftLog"] ↦ l ∗ ownRaftLog l ls }}
    (App (App (Val #(functions needStorageAppendRespMsg [])) (Val #r)) (Val #rd))
  {{ RET #(decide (ls.uents ≠ [])); r.[raft, go!"raftLog"] ↦ l ∗ ownRaftLog l ls }}

end spec

end EtcdGrove
end Perennial
