/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/SnapshotMetadata__GetIndex.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.SnapshotMetadata__GetIndex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem raftpb.SnapshotMetadata.GetIndex.wp_proof :
    raftpb.SnapshotMetadata.GetIndex.spec (GF := GF) (hG := hG) := by
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
    ihave (⟨%Hq, %Hv⟩ | ⟨#Hq, %Hqn⟩) := cellRO_cases $$ cI
    · subst Hq
      wp_auto
      rw [show (W64 0) = md.Index' from Hv.symm]
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
