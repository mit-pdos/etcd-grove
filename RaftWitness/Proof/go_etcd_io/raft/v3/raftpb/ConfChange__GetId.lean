/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/ConfChange__GetId.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.ConfChange__GetId

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

theorem raftpb.ConfChange.GetId.wp_proof :
    raftpb.ConfChange.GetId.spec (GF := GF) (hG := hG) := by
  constructor
  · intro p dq m
    wp_start as Hm
    iNamed Hm
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    ihave (⟨%Hp, %Hv⟩ | ⟨#Hp, %Hpn⟩) := cellRO_cases $$ cI
    · subst Hp
      wp_auto
      rw [show (W64 0) = m.id from Hv.symm]
      iapply HΦ
      iunfold ownCCV1
      iframe
      iexists uf
      isplitr
      · ipureintro; exact Hnn
      iframe cT cN cI Hcs Hpb
    · wp_if_destruct
      · exact absurd rfl Hpn
      · iapply HΦ
        iunfold ownCCV1
        iframe
        iexists uf
        isplitr
        · ipureintro; exact Hnn
        iframe cT cN cI Hcs Hpb
  · wp_start
    wp_auto
    iapply HΦ; ipureintro; trivial

end proof

end EtcdGrove
end Perennial
