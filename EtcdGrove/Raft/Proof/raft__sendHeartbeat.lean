/-
Port of `election_proof/proof_raft__sendHeartbeat.v`.
-/
import EtcdGrove.Raft.Spec.raft__sendHeartbeat
import EtcdGrove.Raft.Spec.raft__send
import EtcdGrove.Raft.Spec.Progress__SentCommit

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- The lookup hits (`to ∈ cfg`; same steps as `maybeSendAppend`). `pr.Match` is read
with `pr` borrowed by its key (`ownRaftPhys_pr`), `r.raftLog.committed` through the
log's record (`ownRaftLog_struct`), `min` by `wp_min2_uint64`. `send` changes only the
outbox, so `pr` is still at `p` for `SentCommit`, which writes only `sentCommit`
(`prvalsMatch_insert_same`). -/
theorem raft.sendHeartbeat.wp_proof
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG))
    (wp_Progress_SentCommit : tracker.Progress.SentCommit.spec (GF := GF) (hG := hG)) :
    raft.sendHeartbeat.spec (GF := GF) (hG := hG) := by
  intro cfg r id s to ctx Hto Hcfg
  wp_start as Hphys
  icases ownRaftPhys_tracker_same $$ Hphys with ⟨%tv, Htrkf, Htrk, Hback⟩
  icases ownTracker_progress_map $$ Htrk with ⟨#Hprs, %Hdom, Htrk⟩
  icases ownTracker_prvals_dom $$ Htrk with ⟨%Hpdom, Htrk⟩
  dsimp only at Hdom Hpdom
  obtain ⟨pr, Hlk⟩ := (GMap.elem_of_dom _ _).1 (Hdom ▸ Hcfg)
  obtain ⟨p, Hpvs⟩ := (GMap.elem_of_dom _ _).1 (Hpdom ▸ (GMap.elem_of_dom_2 _ _ _ Hlk))
  wp_alloc r_ptr as r; wp_pures; wp_alloc ctx_ptr as ctx; wp_pures; wp_alloc to_ptr as to; wp_pures
  wp_load; wp_load; wp_pures; wp_load
  ihave Hphys := Hback $$ Htrkf Htrk
  wp_apply wp_map_lookup1 $$ Hprs as -
  wp_pures; wp_alloc pr_ptr as pr; wp_pures; wp_store; wp_pures; wp_load; wp_pures
  rw [Hlk, Option.getD_some]
  -- `pr.Match`, then `r.raftLog.committed`
  icases ownRaftPhys_pr _ _ _ _ _ _ p $$ Hphys %Hlk %Hpvs with ⟨Hpa, Hpback⟩
  iNamed Hpa
  obtain ⟨-, -, Hm, -⟩ := (progressAbs_Some _ _ _).1 Habs
  wp_load; wp_pures; wp_load; wp_pures
  rw [Hm]
  ihave Hphys := Hpback $$ [Hpv Hinfl]
  · iapply ownProgress_intro $$ Hpv Hinfl
    ipureintro; exact Habs
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  wp_pures
  icases ownRaftPhys_log_same $$ Hphys with ⟨Hlog, Hlogback⟩
  icases ownRaftLog_struct $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
  wp_load; wp_pures
  ihave Hlog := Hlb $$ Hl
  ihave Hphys := Hlogback $$ Hlog
  wp_apply wp_min2_uint64
  wp_pures; wp_alloc commit_ptr as commit; wp_pures; wp_store; wp_pures; wp_load; wp_pures; wp_load
  wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear r ctx to
  let c := w64Min p.matched lv.committed'
  let hb : raftpb.Message :=
    { Type' := W32 8, To' := to, From' := 0, Term' := 0, LogTerm' := 0, Index' := 0,
      Entries' := slice.nil, Commit' := c, Vote' := 0, Snapshot' := null, Reject' := false,
      RejectHint' := 0, Context' := ctx, Responses' := slice.nil }
  have Hok : SendOk id s hb []
      [Msg.mk .heartbeat id to s.term false (W64 0) (W64 0) c (W64 0) []] :=
    Or.inr (Or.inl ⟨.heartbeat, Or.inr (Or.inl rfl), rfl, rfl, Hto, rfl⟩)
  wp_apply wp_raft_send cfg r id s hb [] _ (Or.inl rfl) Hok $$ [$Hphys] as Hphys
  · isplitr
    · iapply ownSlice_nil
    · iapply send_no_snap
      exact (by decide : W32 8 ≠ W32 7)
  wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear pr commit
  icases ownRaftPhys_pr_upd _ _ _ _ _ _ p $$ Hphys %Hlk %Hpvs with ⟨Hpa, Hpback⟩
  wp_apply wp_Progress_SentCommit $$ [$Hpa] as Hpa
  wp_pures
  ihave Hphys := Hpback $$ Hpa
  iapply HΦ $$ %c %_
  iframe Hphys
  obtain ⟨Hlv1, -⟩ := Hlv
  have Hmin : uint.Z c = min (uint.Z p.matched) (uint.Z lv.committed') := w64Min_spec _ _
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
