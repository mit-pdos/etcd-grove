/-
Port of `election_proof/proof_raft__loadState.v`.
-/
import EtcdGrove.Raft.ElectionProof.Spec.raft__loadState
import EtcdGrove.Raft.ElectionProof.Spec.raftLog__lastIndex

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

theorem raft.loadState.wp_proof
    (wp_raftLog_lastIndex : raftLog.lastIndex.spec (GF := GF) (hG := hG)) :
    raft.loadState.spec (GF := GF) (hG := hG) := by
  intro cfg r id s hs Hc
  obtain ⟨term, vote, lead, role, votes, outbox, stepfn, progress, log, logst, prvals,
    prevote⟩ := s
  obtain ⟨prev, sents, uents, lcm, lap, snap, lip, lapg, lpend, lasz, lamx⟩ := logst
  dsimp only at Hc ⊢
  wp_start as Hphys
  wp_auto
  -- Each `r.raftLog.f` loads the pointer through the struct first, so the log is taken
  -- out and put back around each use; the first two put it back unchanged.
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_same $$ Hphys with ⟨HL, Hlogback⟩
  ihave ⟨%Hnw, HL⟩ := ownRaftLog_nowrap $$ HL
  icases ownRaftLog_struct $$ HL with ⟨%lv, Hl, %Hlv, HLback⟩
  dsimp only at Hnw Hlv
  wp_auto
  ihave HL := HLback $$ Hl
  ihave Hphys := Hlogback $$ HL
  have Hll : uint.Z (logLast ⟨prev, sents, uents, lcm, lap, snap, lip, lapg, lpend, lasz, lamx⟩)
      = uint.Z prev.index' + (sents.length : Int) + (uents.length : Int) := by
    simp only [logLast]; word
  rw [Hll] at Hc
  rw [decide_eq_false (by rw [Hlv.1]; omega)]
  wp_auto
  -- `r.raftLog.lastIndex()`
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_same $$ Hphys with ⟨HL, Hlogback⟩
  wp_apply wp_raftLog_lastIndex $$ [$HL] as %li ⟨HL, %Hli⟩
  ihave Hphys := Hlogback $$ HL
  dsimp only at Hli
  rw [decide_eq_false (by omega)]
  wp_auto
  -- `r.raftLog.committed = state.Commit`
  wp_apply raft.wp_load_raftLog $$ Hphys as Hphys
  icases ownRaftPhys_log_at $$ Hphys with ⟨HL, Hlogback⟩
  dsimp only
  icases (ownRaftLog_unfold _ _ _ _ _ _ _ _ _ _ _ _).1 $$ HL with
    ⟨%lv2, Hl, %Hcm2, %Hap2, %Hapg2, %Hip2, %Hasz2, %Hamx2, Hcore⟩
  wp_auto
  iNamed Hcore
  ihave HL : ownRaftLog log
      ⟨prev, sents, uents, hs.Commit', lap, snap, lip, lapg, lpend, lasz, lamx⟩ $$
      [Hl HStorage Huents Huents_cap]
  · reseal_raftLog
    all_goals dsimp only
    all_goals first
      | (intro Hs
         rw [Hcm2] at Hssnap
         exact StoredSnapOk_commit _ _ _ _ _ Hc.1 (Hssnap Hs))
      | omega
      | (simp only [Hcm2, Hap2] at Happlied Happlying ⊢; omega)
  ihave Hphys := Hlogback $$ %_ HL
  wp_apply raft.wp_store_Term $$ Hphys as Hphys
  wp_apply raft.wp_store_Vote $$ Hphys as Hphys
  iapply HΦ
  iexact Hphys

end proof

end EtcdGrove
end Perennial
