/- Lean-first (no Rocq counterpart, 2026-10-13). -/
module

public import Spec.go_etcd_io.raft.v3.getBasicStatus

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

/-- The id and `leadTransferee` loads, `hardState()`, `softState()`, then
`r.raftLog.applied`, read from the log's struct (`ownRaftLog_struct`). -/
theorem getBasicStatus.wp_proof
    (wp_raft_hardState : raft.hardState.spec (GF := GF) (hG := hG))
    (wp_raft_softState : raft.softState.spec (GF := GF) (hG := hG)) :
    getBasicStatus.spec (GF := GF) (hG := hG) := by
  intro c r id s
  wp_start as Hphys
  wp_auto
  wp_apply raft.wp_load_idC $$ Hphys as Hphys
  wp_apply raft.wp_load_leadTransfereeC $$ Hphys as Hphys
  wp_apply wp_raft_hardState $$ Hphys as %hp ⟨#Hhs, Hphys⟩
  wp_apply wp_raft_softState $$ Hphys as Hphys
  wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
  icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hback⟩
  icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
  wp_auto
  ihave Hlog := Hlb $$ Hl
  ihave Hphys := Hback $$ Hlog
  rw [Hlv.2]
  unfold basicStatusOf
  iapply HΦ
  iframe Hhs Hphys

end proof

end EtcdGrove
end Perennial
