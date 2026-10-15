/-
Port of `election_proof/proof_isHardStateEqual.v`.
-/
module

public import Raft37.Spec.go_etcd_io.raft.v3.isHardStateEqual
public import Raft37.Proof.go_etcd_io.raft.v3.LemmasMiscR

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

theorem isHardStateEqual.wp_proof
    (wp_HardState_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG))
    (wp_HardState_GetVote : raftpb.HardState.GetVote.spec (GF := GF) (hG := hG))
    (wp_HardState_GetCommit : raftpb.HardState.GetCommit.spec (GF := GF) (hG := hG)) :
    isHardStateEqual.spec (GF := GF) (hG := hG) := by
  intro a b ha hb
  wp_start as ⟨#Ha, #Hb⟩
  wp_auto
  wp_apply wp_hsOpt_GetTerm wp_HardState_GetTerm a ha $$ [$Ha]
  wp_apply wp_hsOpt_GetTerm wp_HardState_GetTerm b hb $$ [$Hb]
  wp_if_destruct
  · wp_apply wp_hsOpt_GetVote wp_HardState_GetVote a ha $$ [$Ha]
    wp_apply wp_hsOpt_GetVote wp_HardState_GetVote b hb $$ [$Hb]
    wp_if_destruct
    · wp_apply wp_hsOpt_GetCommit wp_HardState_GetCommit a ha $$ [$Ha]
      wp_apply wp_hsOpt_GetCommit wp_HardState_GetCommit b hb $$ [$Hb]
      ispecialize HΦ $$ []
      · itrivial
      iExactEq HΦ
      congr 2 <;> simp_all
    · ispecialize HΦ $$ []
      · itrivial
      iExactEq HΦ
      congr 2 <;> simp_all
  · ispecialize HΦ $$ []
    · itrivial
    iExactEq HΦ
    congr 2 <;> simp_all

end proof

end EtcdGrove
end Perennial
