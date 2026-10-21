/-
Port of `election_proof/proof_MustSync.v` (857d09190).
-/
module

public import Proof.go_etcd_io.raft.v3.LemmasMiscR
public import Spec.go_etcd_io.raft.v3.MustSync

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

theorem MustSync.wp_proof
    (wp_HardState_GetVote : raftpb.HardState.GetVote.spec (GF := GF) (hG := hG))
    (wp_HardState_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG)) :
    MustSync.spec (GF := GF) (hG := hG) := by
  intro st prevst hs phs n
  wp_start as ⟨#Hst, #Hprev⟩
  wp_auto
  wp_if_destruct
  · wp_apply wp_hsOpt_GetVote wp_HardState_GetVote st hs $$ [$Hst]
    wp_apply wp_hsOpt_GetVote wp_HardState_GetVote prevst phs $$ [$Hprev]
    wp_if_destruct
    · wp_apply wp_hsOpt_GetTerm wp_HardState_GetTerm st hs $$ [$Hst]
      wp_apply wp_hsOpt_GetTerm wp_HardState_GetTerm prevst phs $$ [$Hprev]
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
