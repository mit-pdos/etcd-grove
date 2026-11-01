/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/image__applySnapshot.lean`.
Lean-first (no Rocq counterpart): the image's snapshot index read (refused at a non-zero index at
least the new one's); otherwise the snapshot cloned (`proto.Clone`) and frozen read-only, the log's
start set to its index and term, the entries emptied.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.image__applySnapshot
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetTerm
public import Spec.google_golang_org.protobuf.proto.CloneSnapshot
public import Proof.go_etcd_io.raft.v3.LemmasEnts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem image.applySnapshot.wp_proof
    (wp_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.SnapshotMetadata.GetTerm.spec (GF := GF) (hG := hG))
    (wp_Clone : proto.CloneSnapshot.spec (GF := GF) (hG := hG)) :
    image.applySnapshot.spec (GF := GF) (hG := hG) := by
  intro p I sp dq sv eood
  wp_start as ⟨Himg, Hsv, #Herr⟩
  iunfold ownImage at Himg
  icases Himg with ⟨%hsp, %sp0, %es, Himg⟩
  iNamed Himg
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_GetMetadata.1 sp0 DFrac.discard I.snap $$ [$Hpb $HsnapO] as %pm0 ⟨#Hsm0, -⟩
  wp_apply wp_GetIndex pm0 DFrac.discard I.snap.Metadata' $$ [$Hpb $Hsm0] as -
  -- (refused only at a non-zero index at least the new one's; the two ways on meet)
  wp_if_destruct
  have Hst : ¬ imgSnapStale I sv := fun h => h.1 (by simpa using Hif)
  rotate_left
  have Hnz : I.snap.Metadata'.Index' ≠ W64 0 := by simpa using Hif
  wp_apply wp_GetMetadata.1 sp dq sv $$ [$Hpb $Hsv] as %pm ⟨Hsm, Hback⟩
  wp_apply wp_GetIndex pm dq sv.Metadata' $$ [$Hpb $Hsm] as Hsm
  ihave Hsv := Hback $$ Hsm
  wp_if_destruct
  · -- `ErrSnapOutOfDate`
    have Hst : imgSnapStale I sv := ⟨Hnz, by word⟩
    iapply HΦ
    iframe Hsv
    rw [ite_eq_left Hst]
    isplitr
    · ipureintro; rfl
    iunfold ownImage
    iexists hsp, sp0, es
    iframe # ∗
    ipureintro; exact Hwf
  have Hst : ¬ imgSnapStale I sv := fun h => Hif (by have := h.2; word)
  all_goals
    wp_apply wp_Clone.1 sp dq sv $$ [$Hsv] as %sp' ⟨Hsv, Hsn⟩
    imod ownSnapM_persist $$ Hsn with #Hsn
    wp_apply wp_GetMetadata.1 sp dq sv $$ [$Hpb $Hsv] as %pm1 ⟨Hsm, Hback⟩
    wp_apply wp_GetIndex pm1 dq sv.Metadata' $$ [$Hpb $Hsm] as Hsm
    ihave Hsv := Hback $$ Hsm
    wp_apply wp_GetMetadata.1 sp dq sv $$ [$Hpb $Hsv] as %pm2 ⟨Hsm, Hback⟩
    wp_apply wp_GetTerm pm2 dq sv.Metadata' $$ [$Hpb $Hsm] as Hsm
    ihave Hsv := Hback $$ Hsm
    try wp_auto
    iapply HΦ
    iframe Hsv
    rw [ite_eq_right Hst]
    isplitr
    · ipureintro; rfl
    iunfold ownImage
    iexists hsp, sp', slice.nil
    simp only [imgApplySnapshot]
    iframe # ∗
    isplitl []
    · iapply entsPts_nil
    ipureintro; simp only [List.length_nil, Nat.add_zero]; word

end proof

end kvdurable
end EtcdGrove
end Perennial
