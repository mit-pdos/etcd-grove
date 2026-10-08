/-
Port of election_proof/proof_raft__handleHeartbeat.v.
-/
import EtcdGrove.Raft.Spec.raft__handleHeartbeat
import EtcdGrove.Raft.Spec.raftLog__commitTo
import EtcdGrove.Raft.Spec.raft__send

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
/-- `commitTo` on the log taken out with `ownRaftPhys_log_at` and put back at the new
`committed`; then `send` of the literal under `SendOk`'s clause (b). The literal's
`Entries` is `slice.nil`, so `ents = []` (`ownSlice_nil`). -/
theorem raft.handleHeartbeat.wp_proof
    (wp_raftLog_commitTo : raftLog.commitTo.spec (GF := GF) (hG := hG))
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG)) :
    raft.handleHeartbeat.spec (GF := GF) (hG := hG) := by
  intro cfg r id s m Hcommit Hfrom
  wp_start as Hphys
  iNamed Hphys
  wp_alloc r_ptr as r; wp_pures; wp_alloc m_ptr as m; wp_pures; wp_load; wp_pures; wp_load; wp_pures
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  wp_pures
  icases ownRaftPhys_log_at cfg r id s $$ Hphys with ⟨Hlog, Hlogback⟩
  wp_apply wp_raftLog_commitTo _ _ _ Hcommit $$ [$Hlog] as Hlog
  wp_pures; wp_load; wp_pures; wp_load; wp_pures; wp_load; wp_pures; iclear r m
  ihave Hphys := Hlogback $$ Hlog
  let hb : raftpb.Message :=
    { Type' := W32 9, To' := m.From', From' := 0, Term' := 0, LogTerm' := 0, Index' := 0,
      Entries' := slice.nil, Commit' := 0, Vote' := 0, Snapshot' := null, Reject' := false,
      RejectHint' := 0, Context' := m.Context', Responses' := slice.nil }
  have Hok : ∀ s', SendOk id s' hb [] [Msg.plain .heartbeatResp id m.From' s'.term false] :=
    fun s' => Or.inr (Or.inl ⟨.heartbeatResp, Or.inr (Or.inr (Or.inr rfl)), rfl, rfl, Hfrom, rfl⟩)
  wp_apply wp_raft_send cfg r id _ hb [] _ (Or.inl rfl) (Hok _) $$ [$Hphys] as Hphys
  · isplitr
    · iapply ownSlice_nil
    · iapply send_no_snap
      exact (by decide : W32 9 ≠ W32 7)
  wp_pures
  iapply HΦ
  iapply ownRaftPhys_eq cfg r id _ (heartbeatResult id s m) (by cases s; rfl) $$ Hphys

end proof

end EtcdGrove
end Perennial
