/-
Port of election_proof/proof_raft__handleSnapshot.v.

raft v3.7 (stage R4): the message (`msgIn`, taken) lends its snapshot (`GetSnapshot`: owned,
`sn = some sv`); `pb.EnsureSnapshot` hands back the same pointer with its metadata set
(`ownSnapE`), read by `GetMetadata`/`GetIndex`/`GetTerm` (`wp_Snapshot_GetMetadata_E`,
`LemmasSendRB.lean`: R1's `GetMetadata` spec is on `ownSnapM`) and handed to `restore`. The
reply `&pb.Message{To: m.From, Type: MsgAppResp.Enum(), Index: new(...)}` shares the request's
`From` cell.
-/
module

public import Raft37.Spec.go_etcd_io.raft.v3.raft__handleSnapshot
public import Raft37.Spec.go_etcd_io.raft.v3.raft__restore
public import Raft37.Spec.go_etcd_io.raft.v3.raftLog__lastIndex
public import Raft37.Spec.go_etcd_io.raft.v3.raft__send
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.Message__GetSnapshot
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.EnsureSnapshot
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetTerm
public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Raft37.Proof.go_etcd_io.raft.v3.LemmasSendRB

@[expose] public section

set_option linter.unusedSectionVars false

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
    SendOk id s ⟨W32 4, dst, 0, 0, 0, idx, 0, 0, false, 0⟩
      [] [] [appResp id s dst false idx (W64 0) (W64 0)] :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, fun h => absurd h Hdst, rfl⟩)))

/-- The snapshot the message holds is the one `restore` gets (`EnsureSnapshot` of a non-`nil`
pointer is the pointer). Then `restore`'s three exits: on `true` (a restore) the reply carries
`lastIndex()`, the snapshot's index; on `false` it carries `committed`, the old one
(obsolete) or the snapshot's (fast-forward). Each `send` is `SendOk`'s `MsgAppResp`
clause with no entries, as in `handleAppendEntries`. -/
theorem raft.handleSnapshot.wp_proof
    (wp_raft_restore : raft.restore.spec (GF := GF) (hG := hG))
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG))
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG))
    (wp_GetSnapshot : raftpb.Message.GetSnapshot.spec (GF := GF) (hG := hG))
    (wp_EnsureSnapshot : raftpb.EnsureSnapshot.spec (GF := GF) (hG := hG))
    (wp_SnapshotMetadata_GetIndex : raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG))
    (wp_SnapshotMetadata_GetTerm : raftpb.SnapshotMetadata.GetTerm.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    raft.handleSnapshot.spec (GF := GF) (hG := hG) := by
  intro c r id s ml m ents sn ctx rs sv cl Hrole Hvotes Hsn Hcl Hin Hscope Hfid
  subst Hsn
  wp_start as H
  iNamed H
  wp_auto
  wp_apply wp_GetSnapshot.1 $$ [$Hm] as %ps ⟨Hsnap, Hmback⟩
  ihave %Hps : ⌜ps ≠ null⌝ $$ [Hsnap]
  · simp only [snapOpt]; iunfold ownSnapM at Hsnap; iNamed Hsnap; ipureintro; exact Hnn
  wp_apply wp_EnsureSnapshot $$ [$Hsnap] as %sp ⟨Hsnap, %Hsp⟩
  obtain rfl := Hsp Hps
  simp only [Option.getD_some]
  wp_apply wp_Snapshot_GetMetadata_E $$ [$Hsnap] as %pm ⟨Hmd, Hsback⟩
  icases smPts_not_null $$ Hmd with ⟨%Hpm, Hmd⟩
  wp_apply wp_SnapshotMetadata_GetIndex pm _ _ $$ [Hmd] as Hmd
  · iunfold smOpt; iright; iexact Hmd
  ihave Hsnap := Hsback $$ [Hmd]
  · iapply smOpt_not_null _ _ _ Hpm $$ Hmd
  wp_apply wp_Snapshot_GetMetadata_E $$ [$Hsnap] as %pm ⟨Hmd, Hsback⟩
  icases smPts_not_null $$ Hmd with ⟨%Hpm, Hmd⟩
  wp_apply wp_SnapshotMetadata_GetTerm pm _ _ $$ [Hmd] as Hmd
  · iunfold smOpt; iright; iexact Hmd
  ihave Hsnap := Hsback $$ [Hmd]
  · iapply smOpt_not_null _ _ _ Hpm $$ Hmd
  wp_auto
  wp_apply wp_raft_restore c _ _ _ sp sv cl Hrole Hvotes Hcl Hin Hscope
    $$ [$Hphys $Hsnap] as %b %s1 ⟨Hphys, Hsnap, %Hres⟩
  ihave Hm := Hmback $$ [Hsnap]
  · simp only [snapOpt]; iapply ownSnapE_weaken $$ Hsnap
  generalize Hc1 : restoreCfg c sv cl b = c1
  rcases Hres with ⟨Hst, rfl, rfl⟩ | ⟨Hlt, Hmt, rfl, rfl⟩ | ⟨Hlt, Hnm, rfl, prs, pvs, il, rfl⟩
  · -- obsolete: acknowledge the commit index
    wp_auto
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    icases ownRaftLog_struct $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
    wp_auto
    ihave Hlog := Hlb $$ Hl
    ihave Hphys := Hlogback $$ Hlog
    wp_raft_logC
    icases msgPtsC_From_lend _ _ _ _ _ $$ Hm with ⟨%pfr, HFr, #cFr, HmB⟩
    wp_auto
    ihave Hm := HmB $$ HFr
    rw [show raftpb.MsgAppResp = #((W32 4 : raftpb.MessageType)) from rfl]
    haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
    wp_apply wp_MessageType_Enum (W32 4)
    iintro %pty Hpty
    imod cellRO_alloc $$ Hpty with #cTy
    try wp_auto
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    icases ownRaftLog_struct $$ Hlog with ⟨%lv2, Hl, %Hlv2, Hlb⟩
    wp_auto
    ihave Hlog := Hlb $$ Hl
    ihave Hphys := Hlogback $$ Hlog
    imod cellRO_alloc $$ «$v2» with #cIx
    imod msgOwn_lit0 «$a0_ptr» _ ⟨W32 4, m.From', 0, 0, 0, lv2.committed', 0, 0, false, 0⟩ ⊤
      $$ [«$a0»] with Hr
    · iframe «$a0» cTy cFr cIx
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      msg_nulls
    rw [Hlv2.1]
    wp_apply wp_raft_send _ _ _ _ _ _ [] none [] [] _ (Or.inl rfl)
      (appResp_sendOk id s1 m.From' s1.logst.committed Hfid) (fun h => absurd h (by simp [MsgSnap]))
      $$ [$Hphys $Hr] as Hphys
    iapply HΦ $$ %_ %c1
    iframe Hphys
    isplitr
    · ipureintro
      exact Or.inl ⟨Hst, rfl⟩
    ipureintro
    simp only [restoreCfg, Bool.false_eq_true, ↓reduceIte] at Hc1
    exact Or.inr ⟨fun h => absurd Hst (Int.not_le.2 h.1), Hc1.symm⟩
  · -- fast-forward: acknowledge the new commit index, the snapshot's
    wp_auto
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    icases ownRaftLog_struct $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
    wp_auto
    ihave Hlog := Hlb $$ Hl
    ihave Hphys := Hlogback $$ Hlog
    wp_raft_logC
    icases msgPtsC_From_lend _ _ _ _ _ $$ Hm with ⟨%pfr, HFr, #cFr, HmB⟩
    wp_auto
    ihave Hm := HmB $$ HFr
    rw [show raftpb.MsgAppResp = #((W32 4 : raftpb.MessageType)) from rfl]
    haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
    wp_apply wp_MessageType_Enum (W32 4)
    iintro %pty Hpty
    imod cellRO_alloc $$ Hpty with #cTy
    try wp_auto
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    icases ownRaftLog_struct $$ Hlog with ⟨%lv2, Hl, %Hlv2, Hlb⟩
    wp_auto
    ihave Hlog := Hlb $$ Hl
    ihave Hphys := Hlogback $$ Hlog
    imod cellRO_alloc $$ «$v2» with #cIx
    imod msgOwn_lit0 «$a0_ptr» _ ⟨W32 4, m.From', 0, 0, 0, lv2.committed', 0, 0, false, 0⟩ ⊤
      $$ [«$a0»] with Hr
    · iframe «$a0» cTy cFr cIx
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      msg_nulls
    rw [Hlv2.1]
    wp_apply wp_raft_send _ _ _ _ _ _ [] none [] [] _ (Or.inl rfl)
      (appResp_sendOk id _ m.From' sv.Metadata'.Index' Hfid) (fun h => absurd h (by simp [MsgSnap]))
      $$ [$Hphys $Hr] as Hphys
    iapply HΦ $$ %_ %c1
    iframe Hphys
    isplitr
    · ipureintro
      exact Or.inr (Or.inl ⟨Hlt, Hmt, rfl⟩)
    ipureintro
    simp only [restoreCfg, Bool.false_eq_true, ↓reduceIte] at Hc1
    exact Or.inr ⟨fun h => h.2 Hmt, Hc1.symm⟩
  · -- a restore: acknowledge the new last index, the snapshot's
    wp_auto
    wp_apply raft.wp_load_idC $$ Hphys as Hphys
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    icases ownRaftLog_struct $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
    wp_auto
    ihave Hlog := Hlb $$ Hl
    ihave Hphys := Hlogback $$ Hlog
    wp_raft_logC
    icases msgPtsC_From_lend _ _ _ _ _ $$ Hm with ⟨%pfr, HFr, #cFr, HmB⟩
    wp_auto
    ihave Hm := HmB $$ HFr
    rw [show raftpb.MsgAppResp = #((W32 4 : raftpb.MessageType)) from rfl]
    haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
    wp_apply wp_MessageType_Enum (W32 4)
    iintro %pty Hpty
    imod cellRO_alloc $$ Hpty with #cTy
    try wp_auto
    wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
    icases ownRaftPhysC_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
    wp_apply wp_raftLog_lastIndex $$ [$Hlog] as %li ⟨Hlog, %Hli⟩
    ihave Hphys := Hlogback $$ Hlog
    have Hli' : li = sv.Metadata'.Index' := by
      apply uint_Z_inj.1
      simp only [logRestore, List.length_nil, Int.natCast_zero, Int.add_zero] at Hli
      exact Hli
    subst Hli'
    try wp_auto
    imod cellRO_alloc $$ «$v2» with #cIx
    try wp_auto
    imod msgOwn_lit0 «$a0_ptr» _ ⟨W32 4, m.From', 0, 0, 0, sv.Metadata'.Index', 0, 0, false, 0⟩ ⊤
      $$ [«$a0»] with Hr
    · iframe «$a0» cTy cFr cIx
      isplitr
      · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      msg_nulls
    wp_apply wp_raft_send _ _ _ _ _ _ [] none [] [] _ (Or.inl rfl)
      (appResp_sendOk id _ m.From' sv.Metadata'.Index' Hfid) (fun h => absurd h (by simp [MsgSnap]))
      $$ [$Hphys $Hr] as Hphys
    iapply HΦ $$ %_ %c1
    iframe Hphys
    isplitr
    · ipureintro
      exact Or.inr (Or.inr ⟨Hlt, Hnm, prs, pvs, il, rfl⟩)
    ipureintro
    simp only [restoreCfg, ↓reduceIte] at Hc1
    exact Or.inl ⟨⟨Hlt, Hnm⟩, Hc1.symm⟩

end proof

end EtcdGrove
end Perennial
