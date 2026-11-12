/- Lean-first (no Rocq counterpart). -/
module

public import Spec.go_etcd_io.raft.v3.raft__hardState

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

/-- The commit index is the log struct's (`ownRaftLog_struct`). -/
theorem raft.hardState.wp_proof : raft.hardState.spec (GF := GF) (hG := hG) := by
  intro r id s
  wp_start as Hcore
  unfold ownRaftCore
  icases Hcore with ⟨#Hid, HT, HV, HS, HL, Hlog⟩
  wp_auto
  icases ownRaftLog_struct _ _ $$ Hlog with ⟨%lv, Hl, %Hlv, Hlb⟩
  iapply wp_fupd
  wp_auto
  ihave Hlog := Hlb $$ Hl
  imod cellRO_alloc $$ «$v0» with #cT
  imod cellRO_alloc $$ «$v1» with #cV
  imod cellRO_alloc $$ «$v2» with #cC
  irename «$r0» => Hp
  generalize «$r0_ptr» = p at *
  imod hsRO_of_struct p (raftpb.HardState.mk zeroValDef «$v0_ptr» «$v1_ptr» «$v2_ptr» slice.nil 0) (hardstateVal (nodeHardstate s)) ⊤ rfl $$ [Hp] with #Hhs
  · iframe Hp
    rw [Hlv.1]
    simp only [hardstateVal, nodeHardstate]
    iframe cT cV cC
  imodintro
  iapply HΦ
  iframe Hhs
  iframe
  iframe Hid

end proof

end EtcdGrove
end Perennial
