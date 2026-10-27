/-
Port of election_proof/proof_unstable__maybeFirstIndex.v.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.unstable__maybeFirstIndex
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex

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

theorem unstable.maybeFirstIndex.wp_proof
    (wp_Snapshot_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_SnapshotMetadata_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG)) :
    unstable.maybeFirstIndex.spec (GF := GF) (hG := hG) := by
  intro u us
  wp_start as Hpre
  iNamed Hpre
  open_unstable
  wp_auto
  rcases snap_some_or_none us.snap with ⟨sid, Hs⟩ | Hs
  · -- a pending snapshot: `snapshot.GetMetadata().GetIndex() + 1`
    icases ownSnap_of_eq_some Hs $$ Hsnap with ⟨%sv, #Hsv, %Hmeta⟩
    ihave %Hnn : ⌜uv.snapshot' ≠ null⌝ $$ [Hsv]
    · iunfold ownSnapM at Hsv; iNamed Hsv; ipureintro; exact Hnn
    wp_if_destruct
    · exact absurd Hif Hnn
    wp_apply wp_Snapshot_GetMetadata.1 _ DFrac.discard sv $$ [$Hsv] as %pm ⟨#Hm, -⟩
    wp_apply wp_SnapshotMetadata_GetIndex _ DFrac.discard _ $$ [$Hm] as -
    iapply HΦ
    isplitl
    · close_unstable
    ipureintro
    rw [Hs]
    refine ⟨by simp, ?_⟩
    rintro _ ⟨⟩
    rw [Hmeta.1]
  · ihave %Hns := ownSnap_of_eq_none Hs $$ Hsnap
    wp_if_destruct
    · iapply HΦ
      isplitl
      · close_unstable
      ipureintro
      simp [Hs]
    · exact absurd Hns Hif

end proof

end EtcdGrove
end Perennial
