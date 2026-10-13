/-
Port of election_proof/proof_raft__handleHeartbeat.v.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__handleHeartbeat
public import Spec.go_etcd_io.raft.v3.raftLog__commitTo
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
/-- `commitTo` on the log taken out with `ownRaftPhys_log_at` and put back at the new
`committed`; then `send` of the literal under `SendOk`'s clause (b). The literal's
`Entries` is `slice.nil`, so `ents = []` (`ownSlice_nil`). -/
theorem raft.handleHeartbeat.wp_proof
    (wp_raftLog_commitTo : raftLog.commitTo.spec (GF := GF) (hG := hG))
    (wp_raft_send : raft.send.spec (GF := GF) (hG := hG)) :
    raft.handleHeartbeat.spec (GF := GF) (hG := hG) := by
  intro cfg r id s m cl Hcommit Hfrom
  wp_start as Hphys
  iNamed Hphys
  wp_auto
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_at cfg r id s $$ Hphys with ⟨Hlog, %Hgh0, Hlogback⟩
  wp_apply wp_raftLog_commitTo _ _ _ Hcommit $$ [$Hlog] as Hlog
  ihave Hphys := Hlogback $$ Hlog %(LogGhOk.of_fields Hgh0 rfl rfl rfl rfl rfl)
  try wp_auto
  let hb : raftpb.Message :=
    { Type' := W32 9, To' := m.From', From' := 0, Term' := 0, LogTerm' := 0, Index' := 0,
      Entries' := slice.nil, Commit' := 0, Vote' := 0, Snapshot' := null, Reject' := false,
      RejectHint' := 0, Context' := m.Context', Responses' := slice.nil }
  have Hok : ∀ s', SendOk id s' hb [] cl
      [{ Msg.plain .heartbeatResp id m.From' s'.term false with ctx := cl }] :=
    fun s' => Or.inr (Or.inl ⟨.heartbeatResp, Or.inr (Or.inr (Or.inr rfl)), rfl, rfl, Hfrom, rfl⟩)
  wp_apply (raft.send.spec_simple wp_raft_send) cfg r id _ hb [] cl _ (Or.inl rfl) (Hok _) $$ [$Hphys] as Hphys
  · isplitr
    · iapply ownSlice_nil
    isplitr
    · iexact Hctx
    · iapply send_no_snap
      exact (by decide : W32 9 ≠ W32 7)
  iapply HΦ
  iapply ownRaftPhys_eq cfg r id _ (heartbeatResult id s m cl) (by cases s; rfl) $$ Hphys

end proof

end EtcdGrove
end Perennial
