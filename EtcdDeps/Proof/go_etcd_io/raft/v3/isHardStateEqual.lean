/-
Proof of `Spec/isHardStateEqual.lean`. Lean-first (no Rocq counterpart).
-/
module

public import EtcdDeps.Spec.go_etcd_io.raft.v3.isHardStateEqual
public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.HardState__GetTerm
public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.HardState__GetVote
public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.HardState__GetCommit

@[expose] public section

set_option linter.unusedSectionVars false

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

theorem HardStateModel.eq_iff (a b : HardStateModel) :
    a = b ↔ a.term = b.term ∧ a.vote = b.vote ∧ a.commit = b.commit := by
  cases a; cases b; simp

theorem isHardStateEqual.wp_proof
    (wp_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetVote : raftpb.HardState.GetVote.spec (GF := GF) (hG := hG))
    (wp_GetCommit : raftpb.HardState.GetCommit.spec (GF := GF) (hG := hG)) :
    isHardStateEqual.spec (GF := GF) (hG := hG) := by
  intro a b ha hb
  wp_start as ⟨#Ha, #Hb⟩
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_GetTerm a ha $$ [$Hpb $Ha]
  wp_apply wp_GetTerm b hb $$ [$Hpb $Hb]
  wp_if_destruct
  · wp_apply wp_GetVote a ha $$ [$Hpb $Ha]
    wp_apply wp_GetVote b hb $$ [$Hpb $Hb]
    wp_if_destruct
    · wp_apply wp_GetCommit a ha $$ [$Hpb $Ha]
      wp_apply wp_GetCommit b hb $$ [$Hpb $Hb]
      (try wp_auto)
      iapply HΦ
      ipureintro
      rw [HardStateModel.eq_iff]
      simp_all
    · (try wp_auto)
      iapply HΦ
      ipureintro
      rw [HardStateModel.eq_iff]
      simp_all
  · (try wp_auto)
    (try wp_if_destruct)
    (try wp_auto)
    iapply HΦ
    ipureintro
    rw [HardStateModel.eq_iff]
    simp_all

end proof

end EtcdGrove
end Perennial
