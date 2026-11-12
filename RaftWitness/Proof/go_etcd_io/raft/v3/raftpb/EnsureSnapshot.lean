/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/EnsureSnapshot.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.EnsureSnapshot
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.EnsureSnapshotMetadata

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

theorem raftpb.EnsureSnapshot.wp_proof
    (wp_EnsureSnapshotMetadata : raftpb.EnsureSnapshotMetadata.spec (GF := GF) (hG := hG)) :
    raftpb.EnsureSnapshot.spec (GF := GF) (hG := hG) := by
  intro s o
  wp_start as Hs
  iapply wp_fupd
  cases o with
  | none =>
    simp only [snapOpt]
    icases Hs with %Hp
    subst Hp
    wp_auto
    wp_apply wp_EnsureSnapshotMetadata null
      (SnapshotMetadataM.mk (ConfStateM.mk [] [] [] [] false (W64 0)) (W64 0) (W64 0)) $$ []
      as %rm ⟨Hsm, -⟩
    · iunfold smOpt; ileft; ipureintro; exact ⟨rfl, rfl⟩
    ihave Hn : (slice.nil ↦* ([] : List w8) : IProp GF) $$ []
    · iapply ownSlice_nil
    imod ownSnapW_of_struct «$r0_ptr» { (zero_val raftpb.Snapshot) with Metadata' := rm }
      (SnapshotM.mk [] (SnapshotMetadataM.mk (ConfStateM.mk [] [] [] [] false (W64 0)) (W64 0) (W64 0)))
      ⊤ (by rfl) $$ [«$r0» Hn Hsm] with Hsn
    · dsimp only
      iframe «$r0»
      iframe Hn
      iexact Hsm
    imodintro
    iapply HΦ
    iframe
    ipureintro; intro h; exact absurd rfl h
  | some sn =>
    simp only [snapOpt, Option.getD_some]
    iNamed Hs
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    wp_apply wp_EnsureSnapshotMetadata pm sn.Metadata' $$ [Hm] as %rm ⟨Hsm, %Hrm⟩
    · iexact Hm
    wp_if_destruct
    all_goals try (have e := Hrm Hif; subst e)
    all_goals
      imodintro
      iapply HΦ
      isplitl
      · iunfold ownSnapW
        iexists ds, rm, uf
        isplitr
        · ipureintro; exact Hnn
        iframe
        iframe Hpb
      · ipureintro; intro _; rfl

end proof

end EtcdGrove
end Perennial
