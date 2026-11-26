/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/copyHardState.lean`: the copy's three
cells are fresh (`u64p`) and frozen with its struct (`hsROC_of_struct`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.copyHardState
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.u64p
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetVote
public import Spec.go_etcd_io.raft.v3.raftpb.HardState__GetCommit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem copyHardState.wp_proof (wp_u64p : u64p.spec (GF := GF) (hG := hG))
    (wp_GetTerm : raftpb.HardState.GetTerm.spec (GF := GF) (hG := hG))
    (wp_GetVote : raftpb.HardState.GetVote.spec (GF := GF) (hG := hG))
    (wp_GetCommit : raftpb.HardState.GetCommit.spec (GF := GF) (hG := hG)) :
    copyHardState.spec (GF := GF) (hG := hG) := by
  intro hp oh
  wp_start as Hh
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  iunfold hsOptRO at Hh
  icases Hh with (%Hn | ⟨%h, %Hh, #Hh⟩)
  · obtain ⟨rfl, rfl⟩ := Hn
    wp_auto
    iapply HΦ
    iunfold hsOptRO
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  · obtain ⟨Hnn, rfl⟩ := Hh
    wp_auto
    rw [decide_eq_false Hnn]
    iapply wp_fupd
    wp_auto
    wp_apply wp_GetTerm.1 hp h $$ [$Hpb $Hh]
    wp_apply wp_u64p $$ [$Hpkg] as %pt Ht
    wp_apply wp_GetVote.1 hp h $$ [$Hpb $Hh]
    wp_apply wp_u64p $$ [$Hpkg] as %pv Hv
    wp_apply wp_GetCommit.1 hp h $$ [$Hpb $Hh]
    wp_apply wp_u64p $$ [$Hpkg] as %pc Hc
    ihave %Hn := typedPointsto_not_null $$ «$r0»
    imod hsROC_of_struct «$r0_ptr» (raftpb.HardState.mk zeroValDef pt pv pc slice.nil 0) h ⊤ rfl
      $$ [«$r0» Ht Hv Hc] with #Hc
    · iframe
    ihave #Hc := hsROC_hsRO _ _ $$ Hc
    imodintro
    iapply HΦ
    iunfold hsOptRO
    iright
    iexists h
    iframe Hc
    ipureintro
    exact ⟨Hn, rfl⟩

end proof

end AntHarness
end EtcdGrove
end Perennial
