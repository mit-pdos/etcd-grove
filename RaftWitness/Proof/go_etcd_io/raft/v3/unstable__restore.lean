/- Port of election_proof/proof_unstable__restore.v. -/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.unstable__restore
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import RaftWitness.Spec.google_golang_org.protobuf.proto.CloneSnapshot

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Straight-line: five field stores. raft v3.7: the offset is read through the getters, and the log keeps a fresh clone of `s`
(`log_unstable.go:196`), frozen read-only (`ownSnapM_persist`): it is both `ownSnap`'s and
`pendKsn`'s snapshot. -/
theorem unstable.restore.wp_proof
    (wp_Snapshot_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_SnapshotMetadata_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_proto_CloneSnapshot : proto.CloneSnapshot.spec (GF := GF) (hG := hG)) :
    unstable.restore.spec (GF := GF) (hG := hG) := by
  intro u us sp dq sv
  wp_start as ⟨Hun, Hsp⟩
  iunfold ownUnstable at Hun
  icases Hun with ⟨%uv, Hun⟩
  iNamed Hun
  wp_auto
  wp_apply wp_Snapshot_GetMetadata.1 sp dq sv $$ [$Hsp] as %pm ⟨Hm, Hmback⟩
  wp_apply wp_SnapshotMetadata_GetIndex pm dq _ $$ [$Hm] as Hm
  ihave Hsp := Hmback $$ Hm
  iapply wp_fupd
  wp_apply wp_proto_CloneSnapshot.1 sp dq sv $$ [$Hsp] as %p' ⟨Hsp, Hc⟩
  imod ownSnapM_persist _ _ _ $$ Hc with #Hc
  imodintro
  iapply HΦ
  iframe Hsp
  iapply ownUnstable_intro $$ Hu
  · iapply ownSliceCap_nil
  · iapply entsPts_nil
  · iapply (ownSnap_Some _ _).2
    iexists sv
    iframe Hc
    ipureintro; exact ⟨rfl, rfl⟩
  · unfold pendKsn
    imodintro
    iintro %sid %Hsid
    iexists sv
    iframe Hc
    ipureintro
    exact ⟨by cases Hsid; rfl, List.mem_append_right _ (List.mem_singleton_self _)⟩
  · iexact Hlogger
  · ipureintro; exact ⟨rfl, rfl⟩

end proof

end EtcdGrove
end Perennial
