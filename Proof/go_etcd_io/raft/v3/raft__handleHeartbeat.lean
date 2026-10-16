/-
Port of election_proof/proof_raft__handleHeartbeat.v.

raft v3.7 (stage R4): the request is a pointer at any fraction, read by `GetCommit`/`GetContext`
and given back; the response `&pb.Message{To: m.From, Type: MsgHeartbeatResp.Enum(), Context:
m.GetContext()}` shares the request's `From` cell and `Context` bytes (both read-only), built
owned by `msgOwn_lit` (`LemmasSendR.lean`).
-/
module

public import Spec.go_etcd_io.raft.v3.raft__handleHeartbeat
public import Spec.go_etcd_io.raft.v3.raftLog__commitTo
public import Spec.go_etcd_io.raft.v3.raft__send
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetCommit
public import Spec.go_etcd_io.raft.v3.raftpb.Message__GetContext
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasSendRB

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

theorem raft.handleHeartbeat.wp_proof
    (wp_raftLog_commitTo : raftLog.commitTo.spec (GF := GF) (hG := hG))
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG))
    (wp_GetCommit : raftpb.Message.GetCommit.spec (GF := GF) (hG := hG))
    (wp_GetContext : raftpb.Message.GetContext.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    raft.handleHeartbeat.spec (GF := GF) (hG := hG) := by
  intro c r id s ml dq dqe cap m ents sn cl rs Hcommit Hfrom
  wp_start as H
  iNamed H
  wp_auto
  wp_apply wp_GetCommit.1 $$ [$Hm] as Hm
  wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
  icases ownRaftPhysC_log_at c r id s $$ Hphys with ⟨Hlog, %Hgh0, Hlogback⟩
  wp_apply wp_raftLog_commitTo _ _ _ Hcommit $$ [$Hlog] as Hlog
  ihave Hphys := Hlogback $$ Hlog %(LogGhOk.of_fields Hgh0 rfl rfl rfl rfl rfl)
    %(fun _ => logLast_le_of_fields rfl rfl rfl)
  try wp_auto
  icases msgPtsC_From_lend _ _ _ _ _ $$ Hm with ⟨%pfr, HFr, #cFr, HmB⟩
  wp_auto
  ihave Hm := HmB $$ HFr
  rw [show raftpb.MsgHeartbeatResp = #((W32 9 : raftpb.MessageType)) from rfl]
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 9)
  iintro %pty Hpty
  imod cellRO_alloc $$ Hpty with #cTy
  wp_auto
  wp_apply wp_GetContext.1 $$ [$Hm] as %cs ⟨#Hcs, Hm⟩
  try wp_auto
  imod msgOwn_lit «$a0_ptr» _ ⟨W32 9, m.From', 0, 0, 0, 0, 0, 0, false, 0⟩ cl ⊤ $$ [«$a0»] with Hr
  · iframe «$a0» cTy cFr Hcs
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
    msg_nulls
  have Hok : ∀ s' : NState, SendOk id s' ⟨W32 9, m.From', 0, 0, 0, 0, 0, 0, false, 0⟩ [] cl
      [{ Msg.plain .heartbeatResp id m.From' s'.term false with ctx := cl }] := fun s' =>
    Or.inr (Or.inl ⟨.heartbeatResp, Or.inr (Or.inr (Or.inr rfl)), rfl, rfl, Hfrom, rfl⟩)
  wp_apply wp_raft_send c r id _ «$a0_ptr» _ [] none cl [] _ (Or.inl rfl) (Hok _)
    (fun h => absurd h (by simp [MsgSnap])) $$ [$Hphys $Hr] as Hphys
  try wp_auto
  iapply HΦ
  iframe Hm
  iapply ownRaftPhysC_eq c r id _ (heartbeatResult id s m cl) (by cases s; rfl) $$ Hphys

end proof

end EtcdGrove
end Perennial
