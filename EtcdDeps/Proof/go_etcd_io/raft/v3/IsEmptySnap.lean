/-
Proof of `Spec/IsEmptySnap.lean`. Lean-first (no Rocq counterpart).
-/
module

public import EtcdDeps.Spec.go_etcd_io.raft.v3.IsEmptySnap
public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem IsEmptySnap.wp_proof
    (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG)) :
    IsEmptySnap.spec (GF := GF) (hG := hG) := by
  wp_start
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_GetMetadata $$ [$Hpb]
  wp_apply wp_GetIndex null (W64 0) $$ [$Hpb]
  · ileft; ipureintro; exact ⟨rfl, rfl⟩
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
