/-
Port of `election_proof/proof_raftLog__restore.v`.
-/
module

public import Spec.go_etcd_io.raft.v3.raftLog__restore
public import Spec.go_etcd_io.raft.v3.raftpb.Snapshot__GetMetadata
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetTerm
public import Spec.go_etcd_io.raft.v3.unstable__restore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

private theorem isLoggerVal_open (x : GoInterface) :
    isLoggerVal (GF := GF) x ⊢ ∃ lg, ⌜x = interface.ok lg⌝ ∗ isLogger lg := by
  unfold isLoggerVal; exact .rfl

/-- Straight-line: the `Infof` through `l.logger`, the `committed` store, and
`unstable.restore` on the `unstable` field (lent with a wand taking any new value,
`raftLog_lend_unstable`, at the struct after the store). The log is re-sealed at
`logRestore`: the `Storage` and its state `σ` carried over unchanged, now shadowed
(`LogStoreOk`'s `some` case). -/
theorem raftLog.restore.wp_proof
    (wp_unstable_restore : unstable.restore.spec (GF := GF) (hG := hG))
    (wp_Snapshot_GetMetadata : raftpb.Snapshot.GetMetadata.spec (GF := GF) (hG := hG))
    (wp_SnapshotMetadata_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_SnapshotMetadata_GetTerm : raftpb.SnapshotMetadata.GetTerm.spec (GF := GF) (hG := hG)) :
    raftLog.restore.spec (GF := GF) (hG := hG) := by
  intro l ls sp dq sv Hcmlt Hlt
  wp_start as H
  iNamed H
  iNamed Hlog
  icases isLoggerVal_open _ $$ Hl_logger with ⟨%lg, %Hlg, #Hlgr⟩
  wp_auto
  wp_apply wp_Snapshot_GetMetadata.1 sp dq sv $$ [$Hsnap] as %pm ⟨Hm, Hback⟩
  wp_apply wp_SnapshotMetadata_GetIndex pm dq _ $$ [$Hm] as Hm
  ispecialize Hback $$ Hm
  wp_apply wp_Snapshot_GetMetadata.1 sp dq sv $$ [$Hback] as %pm ⟨Hm, Hback⟩
  wp_apply wp_SnapshotMetadata_GetTerm pm dq _ $$ [$Hm] as Hm
  ispecialize Hback $$ Hm
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  try iintro %_ ⟨_, -⟩
  try wp_auto
  rw [Hlg]
  wp_apply Logger.wp_logf lg _ _ _ (by decide) $$ Hlgr
  wp_apply wp_Snapshot_GetMetadata.1 sp dq sv $$ [$Hback] as %pm ⟨Hm, Hback⟩
  wp_apply wp_SnapshotMetadata_GetIndex pm dq _ $$ [$Hm] as Hm
  ispecialize Hback $$ Hm
  try wp_auto
  icases raftLog_lend_unstable l { lv with controlflowLog'.committed' := sv.Metadata'.Index' } ls Hip
    $$ Hl Huents_cap Huents Husnap Hpksn Hu_logger with ⟨Hun, Hlback⟩
  wp_apply wp_unstable_restore _ _ sp dq sv $$ [$Hun $Hback] as ⟨Hsnap, Hun⟩
  iclear Hu_logger
  icases ownUnstable_reopen _ _ _ $$ Hlback Hun
    with ⟨%uv', Hl, Hents_cap, Hents, #Hsn, #Hpk, #Hu_logger, %Hoff', %Hoip'⟩
  iapply HΦ
  iframe Hsnap
  rw [← Hlg]
  simp only [snapId] at Hcmlt Hlt
  iapply ownRaftLog_intro l { lv with controlflowLog'.committed' := sv.Metadata'.Index', unstable' := uv' }
      lv.storage' σ _ _ (logRestore ls (snapTrip sv sv.Metadata'.ConfState'.lists))
      rfl rfl Hap ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ Hapg ?_ ?_ ?_ ?_ Hpaused Hasz Hamx Hstor
      ⟨Hpend.1, fun h => by simp [logRestore] at h⟩
      (fun h => List.mem_append_left _ (Hsksn h)) ?_ ?_ ?_
    $$ Hl HisStorage HStorage Hsn Hpk Hents Hents_cap Hl_logger Hu_logger
  all_goals simp only [logRestore, snapTrip, snapId, List.append_nil, List.length_nil,
    Int.natCast_zero, Int.add_zero]
  · intro k e h; simp at h
  · word
  · exact ⟨rfl, rfl, by word, by word⟩
  · rw [Hoff']; word
  · constructor <;> omega
  · intro h; cases h
  · omega
  · intro h; cases h
  · exact Hoip'
  · rw [Hoff']; word
  · intro h; cases h
  · omega
  all_goals rfl

end proof

end EtcdGrove
end Perennial
