/-
Proof of `Spec/go_etcd_io/raft/v3/witness__cloneState.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.witness__cloneState
public import RaftWitness.Proof.go_etcd_io.raft.v3.LemmasWitness

@[expose] public section

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

/-- A fresh slice of the source's length, copied into, is the source. -/
theorem copy_full (l : List w64) (n : Nat) (H : l.length = n) :
    l.take (List.replicate n (zero_val w64)).length ++
      (List.replicate n (zero_val w64)).drop l.length = l := by
  subst H; simp

/-- Every field read through the nil-safe getters into fresh cells, the replication sets copied
into fresh slices; the new structs sealed (`whsOwn_of_struct`). -/
theorem witness.cloneState.wp_proof
    (wp_GetState : raftpb.WitnessHardState.GetState.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetVote : raftpb.HardState.GetVote.spec (GF := GF) (hG := hG))
    (wp_GetCommit : raftpb.HardState.GetCommit.spec (GF := GF) (hG := hG))
    (wp_GetLastLogIndex : raftpb.WitnessHardState.GetLastLogIndex.spec (GF := GF) (hG := hG))
    (wp_GetLastLogTerm : raftpb.WitnessHardState.GetLastLogTerm.spec (GF := GF) (hG := hG))
    (wp_GetLastLogSubterm : raftpb.WitnessHardState.GetLastLogSubterm.spec (GF := GF) (hG := hG))
    (wp_GetLead : raftpb.WitnessHardState.GetLead.spec (GF := GF) (hG := hG))
    (wp_GetReplicationSet : raftpb.WitnessHardState.GetReplicationSet.spec (GF := GF) (hG := hG))
    (wp_GetReplicationSetOutgoing :
      raftpb.WitnessHardState.GetReplicationSetOutgoing.spec (GF := GF) (hG := hG)) :
    witness.cloneState.spec (GF := GF) (hG := hG) := by
  intro w dq p σ
  wp_start as ⟨Hst, #Hp⟩
  wp_auto
  wp_apply wp_whsOpt_GetState wp_GetState p σ $$ [$Hp] as %ps1 #Hh1
  wp_apply wp_hsOptW_GetTerm wp_GetTerm ps1 _ σ $$ [$Hh1] as -
  try wp_auto
  wp_apply wp_whsOpt_GetState wp_GetState p σ $$ [$Hp] as %ps2 #Hh2
  wp_apply wp_hsOptW_GetVote wp_GetVote ps2 _ σ $$ [$Hh2] as -
  try wp_auto
  wp_apply wp_whsOpt_GetState wp_GetState p σ $$ [$Hp] as %ps3 #Hh3
  wp_apply wp_hsOptW_GetCommit wp_GetCommit ps3 _ σ $$ [$Hh3] as -
  try wp_auto
  wp_apply wp_whsOpt_GetLastLogIndex wp_GetLastLogIndex p σ $$ [$Hp]
  try wp_auto
  wp_apply wp_whsOpt_GetLastLogTerm wp_GetLastLogTerm p σ $$ [$Hp]
  try wp_auto
  wp_apply wp_whsOpt_GetLastLogSubterm wp_GetLastLogSubterm p σ $$ [$Hp]
  try wp_auto
  wp_apply wp_whsOpt_GetLead wp_GetLead p σ $$ [$Hp]
  try wp_auto
  rename_i pt pv pc
  irename : (pt ↦ σ.term : IProp GF) => Ht
  irename : (pv ↦ σ.vote : IProp GF) => Hv
  irename : (pc ↦ σ.commit : IProp GF) => Hc
  imod cellRO_alloc $$ Ht with #cT
  imod cellRO_alloc $$ Hv with #cV
  imod cellRO_alloc $$ Hc with #cC
  imod cellRO_alloc $$ «$v1» with #cLi
  imod cellRO_alloc $$ «$v2» with #cLt
  imod cellRO_alloc $$ «$v3» with #cLs
  imod cellRO_alloc $$ «$v4» with #cLd
  irename «$v0» => Hhv
  wp_apply wp_whsOpt_GetReplicationSet wp_GetReplicationSet p σ $$ [$Hp] as %srs #Hrs
  ihave %Hl := ownSlice_len _ _ _ $$ Hrs
  try wp_auto
  wp_apply wp_slice_make2 (V := w64) srs.len $$ [] as %d0 ⟨Hd0, -⟩
  · ipureintro; exact Hl.2
  wp_apply wp_whsOpt_GetReplicationSetOutgoing wp_GetReplicationSetOutgoing p σ $$ [$Hp]
    as %sro #Hro
  ihave %Hlo := ownSlice_len _ _ _ $$ Hro
  try wp_auto
  wp_apply wp_slice_make2 (V := w64) sro.len $$ [] as %d1 ⟨Hd1, -⟩
  · ipureintro; exact Hlo.2
  try wp_auto
  iapply wp_fupd
  -- the copies
  wp_apply wp_whsOpt_GetReplicationSet wp_GetReplicationSet p σ $$ [$Hp] as %srs' #Hrs'
  wp_apply wp_slice_copy (V := w64) d0 _ srs' σ.rs DFrac.discard $$ [$Hd0 $Hrs'] as %n0 ⟨-, Hd0, -⟩
  try wp_auto
  wp_apply wp_whsOpt_GetReplicationSetOutgoing wp_GetReplicationSetOutgoing p σ $$ [$Hp]
    as %sro' #Hro'
  wp_apply wp_slice_copy (V := w64) d1 _ sro' σ.rsOut DFrac.discard $$ [$Hd1 $Hro'] as %n1 ⟨-, Hd1, -⟩
  try wp_auto
  rw [copy_full σ.rs _ Hl.1, copy_full σ.rsOut _ Hlo.1]
  imod ownSlice_persist $$ Hd0 with #Hd0
  imod ownSlice_persist $$ Hd1 with #Hd1
  imod whsOwn_of_struct _ _ _ σ ⊤ $$ [«$r0» Hhv] with Hown
  · iframe «$r0» Hhv cT cV cC cLi cLt cLs cLd Hd0 Hd1
    ipureintro; exact ⟨rfl, rfl⟩
  imodintro
  iapply HΦ
  iframe Hst Hown

end proof

end EtcdGrove
end Perennial
