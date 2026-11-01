/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/Storage__Snapshot.lean`. Lean-first (no
Rocq counterpart). raft v3.7 (2026-10-16, stage R6b): the snapshot's emptiness is read through
`GetMetadata`/`GetIndex` on the fresh clone `MemoryStorage.Snapshot` returns; the error
`ErrSnapshotTemporarilyUnavailable` is not `nil` (`isInitialized`, raft's package fact), so a `nil`
error comes with the clone.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.Storage__Snapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Snapshot
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

theorem Storage.Snapshot.wp_proof
    (wp_MemoryStorage_Snapshot : MemoryStorage.Snapshot.spec (GF := GF) (hG := hG))
    (wp_Snapshot_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_SnapshotMetadata_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG)) :
    Storage.Snapshot.spec (GF := GF) (hG := hG) := by
  sorry -- durability stage I (I-5): broken by the MemoryStorage statement changes (mode o, memStorFresh c sv)

end proof

end kv
end EtcdGrove
end Perennial
