/-
Port of election_proof/proof_IsEmptySnap.v.
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.raft.v3.IsEmptySnap

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem IsEmptySnap.wp_proof
    (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG)) :
    IsEmptySnap.spec (GF := GF) (hG := hG) := by
  intro sp dq o
  wp_start as Hsp
  wp_auto
  cases o with
  | none =>
    simp only [snapOpt]
    icases Hsp with %Hsp
    subst Hsp
    wp_apply wp_GetMetadata.2
    wp_apply wp_GetIndex null dq (SnapshotMetadataM.mk (ConfStateM.mk [] [] [] [] false) (W64 0) (W64 0)) $$ []
    · iunfold smOpt; ileft; ipureintro; exact ⟨rfl, rfl⟩
    iintro -
    wp_auto
    iapply HΦ
    isplitr
    · ipureintro; rfl
    ipureintro; rfl
  | some sv =>
    simp only [snapOpt]
    wp_apply wp_GetMetadata.1 sp dq sv $$ [$Hsp] as %pm ⟨Hm, Hback⟩
    wp_apply wp_GetIndex pm dq sv.Metadata' $$ [$Hm] as Hm
    iapply HΦ
    isplitr
    · ipureintro; rfl
    iapply Hback $$ Hm

end proof

end EtcdGrove
end Perennial
