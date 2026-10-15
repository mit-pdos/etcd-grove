/-
Proof of `Raft37/Spec/go_etcd_io/raft/v3/raftpb/SnapshotMetadata__GetTerm.lean`.
-/
module

public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetTerm

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

theorem raftpb.SnapshotMetadata.GetTerm.wp_proof :
    raftpb.SnapshotMetadata.GetTerm.spec (GF := GF) (hG := hG) := by
  intro p dq md
  wp_start as Hm
  iunfold smOpt at Hm
  icases Hm with (⟨%Hp, %Hmd⟩ | Hm)
  · subst Hp Hmd
    wp_auto
    iapply HΦ
    iunfold smOpt
    ileft; ipureintro; exact ⟨rfl, rfl⟩
  · iNamed Hm
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    ihave (⟨%Hq, %Hv⟩ | ⟨#Hq, %Hqn⟩) := cellRO_cases $$ cT
    · subst Hq
      wp_auto
      rw [show (W64 0) = md.Term' from Hv.symm]
      iapply HΦ
      iunfold smOpt
      iright
      iunfold smPts
      iframe
      iexists uf
      isplitr
      · ipureintro; exact Hnn
      iframe cI cT Hpb
    · wp_if_destruct
      · exact absurd rfl Hqn
      · iapply HΦ
        iunfold smOpt
        iright
        iunfold smPts
        iframe
        iexists uf
        isplitr
        · ipureintro; exact Hnn
        iframe cI cT Hpb

end proof

end EtcdGrove
end Perennial
