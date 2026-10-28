/-
Port of `election_proof/proof_raft__sendHeartbeat.v`.

raft v3.7 (stage R4): the heartbeat is `&pb.Message{To: new(to), Type: MsgHeartbeat.Enum(),
Commit: new(commit), Context: ctx}`, built owned (`msgOwn_lit`, `LemmasSendR.lean`).
-/
module

public import Spec.go_etcd_io.raft.v3.raft__sendHeartbeat
public import Spec.go_etcd_io.raft.v3.raft__send
public import Spec.go_etcd_io.raft.v3.tracker.Progress__SentCommit
public import Spec.go_etcd_io.raft.v3.raftpb.MessageType__Enum
public import Proof.go_etcd_io.raft.v3.LemmasSendR

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

/-- The lookup hits (`to ∈ domSet s.progress`; same steps as `maybeSendAppend`). `pr.Match` is read
with `pr` borrowed by its key (`ownRaftPhysC_pr`), `r.raftLog.committed` through the
log's record (`ownRaftLog_struct`), `min` by `wp_min2_uint64`. `send` changes only the
outbox, so `pr` is still at `p` for `SentCommit`, which writes only `sentCommit`
(`prvalsMatch_insert_same`). -/
theorem raft.sendHeartbeat.wp_proof
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG))
    (wp_Progress_SentCommit : tracker.Progress.SentCommit.spec (GF := GF) (hG := hG))
    (wp_MessageType_Enum : raftpb.MessageType.Enum.spec (GF := GF) (hG := hG)) :
    raft.sendHeartbeat.spec (GF := GF) (hG := hG) := by
  intro c r id s to ctx cl Hto Hcfg
  wp_start as H
  iNamed H
  icases ownRaftPhysC_tracker_same $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  icases ownTrackerC_progress_map $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
  icases ownTrackerC_prvals_dom $$ Htrk with ⟨%Hpdom, Htrk⟩
  dsimp only at Hdom Hpdom
  obtain ⟨pr, Hlk⟩ := (GMap.elem_of_dom _ _).1 Hcfg
  obtain ⟨p, Hpvs⟩ := (GMap.elem_of_dom _ _).1 (Hpdom ▸ (GMap.elem_of_dom_2 _ _ _ Hlk))
  wp_auto
  ihave Hphys := Hback $$ Htrkf Htrk
  wp_apply wp_map_lookup1 $$ Hprs as -
  rw [Hlk, Option.getD_some]
  -- `pr.Match`, then `r.raftLog.committed`
  icases ownRaftPhysC_pr _ _ _ _ _ _ p $$ Hphys %Hlk %Hpvs with ⟨Hpa, Hpback⟩
  iNamed Hpa
  obtain ⟨-, -, Hm, -⟩ := (progressAbs_Some _ _ _).1 Habs
  wp_auto
  rw [Hm]
  ihave Hphys := Hpback $$ [Hpv Hinfl]
  · iapply ownProgress_intro $$ Hpv Hinfl
    ipureintro; exact Habs
  wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
  icases ownRaftPhysC_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
  icases ownRaftLog_struct $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
  wp_auto
  ihave Hlog := Hlb $$ Hl
  ihave Hphys := Hlogback $$ Hlog
  wp_apply wp_min2_uint64
  let cm := w64Min p.matched lv.committed'
  rw [show raftpb.MsgHeartbeat = #((W32 8 : raftpb.MessageType)) from rfl]
  haveI : go.NotInterface go.int32 := ⟨by unfold go.int32; trivial⟩
  wp_apply wp_MessageType_Enum (W32 8)
  iintro %pty Hpty
  imod cellRO_alloc $$ Hpty with #cTy
  imod cellRO_alloc $$ «$v0» with #cTo
  wp_auto
  imod cellRO_alloc $$ «$v2» with #cCo
  imod msgOwn_lit «$a0_ptr» _ ⟨W32 8, to, 0, 0, 0, 0, cm, 0, false, 0⟩ cl ⊤ $$ [«$a0»] with Hm
  · iframe «$a0» cTy cTo cCo Hctx
    isplitr
    · ipureintro; exact ⟨rfl, rfl, rfl, rfl⟩
    msg_nulls
  have Hok : SendOk id s ⟨W32 8, to, 0, 0, 0, 0, cm, 0, false, 0⟩ [] cl
      [Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] [] cl] :=
    Or.inr (Or.inl ⟨.heartbeat, Or.inr (Or.inl rfl), rfl, rfl, Hto, rfl⟩)
  wp_apply wp_raft_send c r id s «$a0_ptr» _ [] none cl [] _ (Or.inl rfl) Hok
    (fun h => absurd h (by simp [MsgSnap]))
      (fun h => absurd h (by simp [MsgApp])) rfl $$ [$Hphys $Hm] as Hphys
  · iapply tsSrc_ne; exact (fun h => absurd h (by simp [MsgSnap]))
  icases ownRaftPhysC_pr_upd _ _ _ _ _ _ p $$ Hphys %Hlk %Hpvs with ⟨%Hok, -, Hpa, Hpback⟩
  wp_apply wp_Progress_SentCommit $$ [$Hpa] as Hpa
  ihave Hphys := Hpback $$ %_ Hpa %rfl %(fun Hl => (Hok Hl).sentCommit _)
  iapply HΦ $$ %cm %_
  iframe Hphys
  obtain ⟨Hlv1, -⟩ := Hlv
  have Hmin : uint.Z cm = min (uint.Z p.matched) (uint.Z lv.committed') := w64Min_spec _ _
  ipureintro
  refine ⟨?_, ?_, ?_⟩
  · rw [← Hlv1]; omega
  · simp only [prvalsMatch, GMap.fmap_eq, GMap.lookup_fmap, Hpvs, Option.map_some,
      Option.getD_some]
    omega
  · exact prvalsMatch_insert_same _ _ p _ Hpvs rfl

end proof

end EtcdGrove
end Perennial
