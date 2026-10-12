/-
Port of election_proof/proof_raft__handleSnapshot.v.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__handleSnapshot
public import Spec.go_etcd_io.raft.v3.raft__restore
public import Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import Spec.go_etcd_io.raft.v3.raft__send

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
/-- The reply of every exit: `SendOk`'s `MsgAppResp` clause, with no entries. -/
private theorem appResp_sendOk (id : w64) (s : NState) (dst idx : w64) (Hdst : dst ≠ id) :
    SendOk id s
      { Type' := W32 4, To' := dst, From' := 0, Term' := 0, LogTerm' := 0, Index' := idx,
        Entries' := slice.nil, Commit' := 0, Vote' := 0, Snapshot' := null, Reject' := false,
        RejectHint' := 0, Context' := slice.nil, Responses' := slice.nil }
      [] [] [appResp id s dst false idx (W64 0) (W64 0)] :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, fun h => absurd h Hdst, rfl⟩)))

/-- `m.Snapshot` points to `sv`, so the copy `s = *m.Snapshot` is taken and the `nil`
arm is dead. Then `restore`'s three exits: on `true` (a restore) the reply carries
`lastIndex()`, the snapshot's index; on `false` it carries `committed`, the old one
(obsolete) or the snapshot's (fast-forward). Each `send` is `SendOk`'s `MsgAppResp`
clause with no entries, as in `handleAppendEntries`. -/
theorem raft.handleSnapshot.wp_proof
    (wp_raft_restore : raft.restore.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG)) :
    raft.handleSnapshot.spec (GF := GF) (hG := hG) := by
  intro cfg r id s m sv voters Hrole Hvotes Hin Hscope Hfid
  wp_start as H
  iNamed H
  wp_auto
  ihave %Hnn := typedPointsto_not_null $$ Hsv
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_raft_restore _ _ _ _ sv voters Hrole Hvotes Hin Hscope $$ [$Hphys $Hvoters]
    as %b %s1 ⟨Hphys, %Hres⟩
  rcases Hres with ⟨Hst, rfl, rfl⟩ | ⟨Hlt, Hm, rfl, rfl⟩ | ⟨Hlt, Hnm, rfl, prs, pvs, rfl⟩
  · -- obsolete: acknowledge the commit index
    wp_auto
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
    icases ownRaftPhys_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    icases ownRaftLog_struct $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
    wp_auto
    ihave Hlog := Hlb $$ Hl
    ihave Hphys := Hlogback $$ Hlog
    wp_raft_log
    wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
    icases ownRaftPhys_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    icases ownRaftLog_struct $$ Hlog with ⟨%lv2, Hl, %Hlv2, Hlb⟩
    wp_auto
    ihave Hlog := Hlb $$ Hl
    ihave Hphys := Hlogback $$ Hlog
    rw [Hlv2.1]
    wp_apply wp_raft_send _ _ _ _ _ [] [] _ (Or.inl rfl)
      (appResp_sendOk id s1 m.From' s1.logst.committed Hfid) $$ [$Hphys] as Hphys
    · isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSlice_nil
      · iapply send_no_snap
        exact (by decide : W32 4 ≠ W32 7)
    iapply HΦ
    iframe Hphys
    ipureintro
    exact Or.inl ⟨Hst, rfl⟩
  · -- fast-forward: acknowledge the new commit index, the snapshot's
    wp_auto
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
    icases ownRaftPhys_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    icases ownRaftLog_struct $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
    wp_auto
    ihave Hlog := Hlb $$ Hl
    ihave Hphys := Hlogback $$ Hlog
    wp_raft_log
    wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
    icases ownRaftPhys_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    icases ownRaftLog_struct $$ Hlog with ⟨%lv2, Hl, %Hlv2, Hlb⟩
    wp_auto
    ihave Hlog := Hlb $$ Hl
    ihave Hphys := Hlogback $$ Hlog
    rw [Hlv2.1]
    wp_apply wp_raft_send _ _ _ _ _ [] [] _ (Or.inl rfl)
      (appResp_sendOk id _ m.From' sv.Metadata'.Index' Hfid) $$ [$Hphys] as Hphys
    · isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSlice_nil
      · iapply send_no_snap
        exact (by decide : W32 4 ≠ W32 7)
    iapply HΦ
    iframe Hphys
    ipureintro
    exact Or.inr (Or.inl ⟨Hlt, Hm, rfl⟩)
  · -- a restore: acknowledge the new last index, the snapshot's
    wp_auto
    wp_apply raft.wp_load_id $$ Hphys as Hphys
    wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
    icases ownRaftPhys_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    icases ownRaftLog_struct $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
    wp_auto
    ihave Hlog := Hlb $$ Hl
    ihave Hphys := Hlogback $$ Hlog
    wp_raft_log
    wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
    icases ownRaftPhys_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    wp_apply wp_raftLog_lastIndex $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
    ihave Hphys := Hlogback $$ Hlog
    have Hli' : li = sv.Metadata'.Index' := by
      apply uint_Z_inj.1
      simp only [logRestore, List.length_nil, Int.natCast_zero, Int.add_zero] at Hli
      exact Hli
    subst Hli'
    wp_apply wp_raft_send _ _ _ _ _ [] [] _ (Or.inl rfl)
      (appResp_sendOk id _ m.From' sv.Metadata'.Index' Hfid) $$ [$Hphys] as Hphys
    · isplitr
      · iapply ownSlice_nil
      isplitr
      · iapply ownSlice_nil
      · iapply send_no_snap
        exact (by decide : W32 4 ≠ W32 7)
    iapply HΦ
    iframe Hphys
    ipureintro
    exact Or.inr (Or.inr ⟨Hlt, Hnm, prs, pvs, rfl⟩)

end proof

end EtcdGrove
end Perennial
