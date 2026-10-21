/-
Proof of `Spec/go_etcd_io/raft/v3/raft__sendHeartbeatToWitness.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__sendHeartbeatToWitness

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

/-- The heartbeat appended to the queue (`ownRaftPhysC_witQ`). -/
theorem raft.sendHeartbeatToWitness.wp_proof :
    raft.sendHeartbeatToWitness.spec (GF := GF) (hG := hG) := by
  intro c r id s to ctx cl Hw Hwc
  wp_start as ⟨Hphys, #Hctx⟩
  ihave Hnil : (slice.nil ↦* ([] : List w64) : IProp GF) $$ []
  · iapply ownSlice_nil
  imod ownSlice_persist $$ Hnil with #Hnil
  icases ownRaftPhysC_shared c r id s $$ Hphys with ⟨%lok, #Hfid, -, -, Hphys⟩
  icases ownRaftPhysC_witQ c r id s $$ Hphys with ⟨%wsl, %μs, HT, Hwf, Hq, Hback⟩
  iunfold ownWQueue at Hq
  icases Hq with ⟨%wms, Hqs, Hqcap, #Hqm⟩
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %m_sl ⟨m_sl, -⟩
  try wp_auto
  wp_apply wp_slice_append $$ [Hqs Hqcap m_sl] as %q' ⟨Hqs, Hqcap, -⟩
  · iframe
  try wp_auto
  ihave Hq : ownWQueue (GF := GF) q' (μs ++ [whbMsg id to s.term cl]) $$ [Hqs Hqcap]
  · iunfold ownWQueue
    iexists _
    iframe Hqs Hqcap
    iapply BigSepL2.bigSepL2_snoc.2
    iframe Hqm
    unfold ownWMsg
    simp only [whbMsg]
    iexists slice.nil, slice.nil
    iframe Hnil Hctx
    isplitr
    · ipureintro; simp only [MsgHeartbeat, and_true]; exact ⟨trivial, trivial, trivial, trivial, rfl, rfl, rfl, rfl⟩
    ileft; ipureintro; exact ⟨rfl, trivial⟩
  ihave Hphys := Hback $$ %q' %_ %Hw %(⟨Hwc, rfl, fun _ => Int.le_refl _⟩) HT Hwf Hq
  try wp_auto
  iapply HΦ $$ Hphys

end proof

end EtcdGrove
end Perennial
