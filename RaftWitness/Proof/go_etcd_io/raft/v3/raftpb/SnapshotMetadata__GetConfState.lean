/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/SnapshotMetadata__GetConfState.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetConfState

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

theorem raftpb.SnapshotMetadata.GetConfState.wp_proof :
    raftpb.SnapshotMetadata.GetConfState.spec (GF := GF) (hG := hG) := by
  intro p dq md
  wp_start as Hm
  iunfold smOpt at Hm
  icases Hm with (⟨%Hp, %Hmd⟩ | Hm)
  · subst Hp Hmd
    wp_auto
    iapply HΦ
    isplitr
    · iunfold csOptA
      ileft; ipureintro; exact ⟨rfl, rfl⟩
    · iintro _
      iunfold smOpt
      ileft; ipureintro; exact ⟨rfl, rfl⟩
  · iNamed Hm
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    · iapply HΦ
      iframe Hc
      iintro Hc
      iunfold smOpt
      iright
      iunfold smPts
      iexists pc, pi, pt, uf
      isplitr
      · ipureintro; exact Hnn
      iframe
      iframe cI cT Hpb

end proof

end EtcdGrove
end Perennial
