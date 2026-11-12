/-
Lean-first (no Rocq counterpart): the proof of `makeTracingState`
(`Spec/go_etcd_io/raft/v3/makeTracingState.lean`).
-/
module

public import Spec.go_etcd_io.raft.v3.makeTracingState
public import Spec.go_etcd_io.raft.v3.raft__hardState
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetVote
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetCommit
public import Spec.strconv.FormatUint

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

theorem makeTracingState.wp_proof
    (wp_raft_hardState : raft.hardState.spec (GF := GF) (hG := hG))
    (wp_HardState_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG))
    (wp_HardState_GetVote : raftpb.HardState.GetVote.spec (GF := GF) (hG := hG))
    (wp_HardState_GetCommit : raftpb.HardState.GetCommit.spec (GF := GF) (hG := hG))
    (wp_FormatUint : strconv.FormatUint.spec (GF := GF) (hG := hG)) :
    makeTracingState.spec (GF := GF) (hG := hG) := by
  intro r id s
  wp_start as Hphys
  wp_auto
  wp_apply wp_raft_hardState r id s $$ [$Hphys] as %p ⟨#Hhs, Hphys⟩
  wp_apply wp_HardState_GetTerm.1 $$ [$Hhs]
  wp_apply wp_HardState_GetVote.1 $$ [$Hhs]
  wp_apply wp_FormatUint
  · ipureintro; word
  iintro %str %Hstr
  wp_auto
  wp_apply wp_HardState_GetCommit.1 $$ [$Hhs]
  iapply HΦ
  iframe
  ipureintro
  exact ⟨rfl, Hstr, rfl⟩

end proof

end EtcdGrove
end Perennial
