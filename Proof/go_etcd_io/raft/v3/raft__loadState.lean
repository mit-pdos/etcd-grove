/-
Port of `election_proof/proof_raft__loadState.v`.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__loadState
public import Spec.go_etcd_io.raft.v3.raftLog__lastIndex

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

theorem raft.loadState.wp_proof
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG)) :
    raft.loadState.spec (GF := GF) (hG := hG) := by
  intro cfg r id s hs Hc Hle
  wp_start as Hphys
  wp_auto
  -- Each `r.raftLog.f` loads the pointer through the struct first, so the log is taken
  -- out and put back around each use; the first two put it back unchanged.
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_same $$ Hphys with ⟨HL, Hlogback⟩
  ihave ⟨%Hnw, HL⟩ := ownRaftLog_nowrap $$ HL
  icases ownRaftLog_struct $$ HL with ⟨%lv, Hl, %Hlv, HLback⟩
  wp_auto
  ihave HL := HLback $$ Hl
  ihave Hphys := Hlogback $$ HL
  have Hll : uint.Z (logLast s.logst)
      = uint.Z s.logst.prev.index' + (s.logst.sents.length : Int)
        + (s.logst.uents.length : Int) := by
    simp only [logLast]; word
  rw [Hll] at Hc
  rw [decide_eq_false (by rw [Hlv.1]; omega)]
  wp_auto
  -- `r.raftLog.lastIndex()`
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_same $$ Hphys with ⟨HL, Hlogback⟩
  wp_apply wp_raftLog_lastIndex $$ [$HL] as %li ⟨HL, %Hli⟩
  ihave Hphys := Hlogback $$ HL
  rw [decide_eq_false (by omega)]
  wp_auto
  -- `r.raftLog.committed = state.Commit`
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_at $$ Hphys with ⟨HL, %Hgh0, Hlogback⟩
  iNamed HL
  wp_auto
  ihave HL : ownRaftLog s.log { s.logst with committed := hs.Commit' } $$
      [Hl HStorage Huents Huents_cap]
  · reseal_raftLog
    all_goals first
      | (intro Hs; exact StoredSnapOk_commit _ _ _ _ _ Hc.1 (Hssnap Hs))
      | word
  ihave Hphys := Hlogback $$ %_ HL %(LogGhOk.of_fields Hgh0 rfl rfl rfl rfl rfl)
  wp_apply raft.wp_store_Term cfg r id { s with logst := { s.logst with committed := hs.Commit' } }
    hs.Term' Hle $$ Hphys as Hphys
  wp_apply raft.wp_store_Vote $$ Hphys as Hphys
  iapply HΦ
  iexact Hphys

end proof

end EtcdGrove
end Perennial
