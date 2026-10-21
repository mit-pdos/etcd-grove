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
  wp_apply wp_Snapshot_GetMetadata_S sp dq sv $$ [$Hsnap] as %pm ⟨Hm, Hback⟩
  wp_apply wp_SnapshotMetadata_GetIndex_S pm dq _ $$ [$Hm] as Hm
  ispecialize Hback $$ Hm
  wp_apply wp_Snapshot_GetMetadata_S sp dq sv $$ [$Hback] as %pm ⟨Hm, Hback⟩
  wp_apply wp_SnapshotMetadata_GetTerm_S pm dq _ $$ [$Hm] as Hm
  ispecialize Hback $$ Hm
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  try iintro %_ ⟨_, -⟩
  try wp_auto
  rw [Hlg]
  wp_apply Logger.wp_logf lg _ _ _ (by decide) $$ Hlgr
  wp_apply wp_Snapshot_GetMetadata_S sp dq sv $$ [$Hback] as %pm ⟨Hm, Hback⟩
  wp_apply wp_SnapshotMetadata_GetIndex_S pm dq _ $$ [$Hm] as Hm
  ispecialize Hback $$ Hm
  try wp_auto
  icases raftLog_lend_unstable l { lv with committed' := sv.Metadata'.Index' } ls Hip Hsip
    $$ Hl Huents_cap Huents Husnap Hpksn Hu_logger with ⟨Hun, Hlback⟩
  wp_apply wp_unstable_restore _ _ sp dq sv $$ [$Hun $Hback] as ⟨Hsnap, Hun⟩
  iclear Hu_logger
  icases ownUnstable_reopen _ _ _ $$ Hlback Hun
    with ⟨%uv', Hl, Hents_cap, Hents, #Hsn, #Hpk, #Hu_logger, %Hoff', %Hoip', %Hsip'⟩
  iapply HΦ
  iframe Hsnap
  rw [← Hlg]
  ihave #Hkcert' : ([∗list] k ∈ ls.ksn ++ [snapTrip sv sv.Metadata'.ConfState'.lists],
      storCert (GF := GF) lv.storage' k) $$ []
  · iapply (BigSepL.bigSepL_snoc (Φ := fun _ k => storCert (GF := GF) lv.storage' k)).2
    iframe Hkcert
    rw [Hstor]; iexact Hcert
  simp only [snapId] at Hcmlt Hlt
  iapply ownRaftLog_intro l { lv with committed' := sv.Metadata'.Index', unstable' := uv' }
      lv.storage' σ _ _ (logRestore ls (snapTrip sv sv.Metadata'.ConfState'.lists))
      rfl rfl Hap ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ Hapg ?_ ?_ ?_ ?_ Hpaused Hasz Hamx Hstor
      ⟨Hpend.1, fun h => by simp [logRestore] at h⟩
      ⟨Hfl.1, Hfl.2.1, by
        show uint.Z ls.applying < uint.Z (sv.Metadata'.Index' + W64 1)
        have := Happlying.2; word, Hfl.2.2.2.1, fun _ hl => by
        have Ha := storExt_of_inv Hstore Hoffset Hipb Hpersist Hpend Hfl hl
        show uint.Z (if ls.snap.isSome ∧ uint.Z ls.applying ≤ uint.Z ls.sxt then ls.sxt
            else ls.applying) ≤ _ ∧
          uint.Z ls.applying ≤
            uint.Z (if ls.snap.isSome ∧ uint.Z ls.applying ≤ uint.Z ls.sxt then ls.sxt
              else ls.applying)
        split
        · rename_i hc
          obtain ⟨hs, hle⟩ := hc
          have := Hfl.2.2.2.2 (by intro h; rw [h] at hs; cases hs) hl
          exact ⟨this.1, hle⟩
        · exact ⟨Ha, Int.le_refl _⟩⟩
      (fun h => List.mem_append_left _ (Hsksn h)) Hsip' (fun h => by simp [logRestore] at h)
      -- (D22 S-d1b) the storage stays lent, if it is; no window; the snapshot not in progress
      (fun _ => by simp [logRestore]) ⟨rfl, rfl⟩
      ⟨(fun h => by simp [logRestore] at h), (fun _ _ => ⟨by rw [Hoff']; rfl, by
        show uint.Z ls.applying ≤ uint.Z sv.Metadata'.Index'
        have := Happlying.2; omega⟩)⟩
      (fun h => by simp [logRestore] at h) ?_ ?_ ?_ ?_
    $$ Hl HisStorage HStorage Hsn Hpk Hkcert' Hents Hents_cap Hl_logger Hu_logger
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
