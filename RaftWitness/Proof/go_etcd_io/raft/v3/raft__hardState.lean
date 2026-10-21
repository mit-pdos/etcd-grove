/- Lean-first (no Rocq counterpart). -/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raft__hardState

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

/-- The commit index is the log struct's (`ownRaftLog_struct`). -/
theorem raft.hardState.wp_proof : raft.hardState.spec (GF := GF) (hG := hG) := by
  intro c r id s
  wp_start as Hphys
  wp_auto
  wp_apply raft.wp_load_TermC $$ Hphys as Hphys
  wp_apply raft.wp_load_VoteC $$ Hphys as Hphys
  wp_apply raft.wp_load_raftLogC $$ Hphys as Hphys
  icases ownRaftPhysC_log_same c r id s $$ Hphys with ⟨Hlog, Hback⟩
  icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
  wp_auto
  ihave Hlog := Hlb $$ Hl
  ihave Hphys := Hback $$ Hlog
  imod cellRO_alloc $$ «$v0» with #cT
  imod cellRO_alloc $$ «$v1» with #cV
  imod cellRO_alloc $$ «$v2» with #cC
  wp_alloc p as Hp
  imod hsRO_of_struct p (raftpb.HardState.mk zeroValDef «$v0_ptr» «$v1_ptr» «$v2_ptr» slice.nil 0) (hardstateVal (nodeHardstate s)) ⊤ rfl $$ [Hp] with #Hhs
  · iframe Hp
    rw [Hlv.1]
    simp only [hardstateVal, nodeHardstate]
    iframe cT cV cC
  wp_auto
  iapply HΦ
  iframe Hhs Hphys

end proof

end EtcdGrove
end Perennial
