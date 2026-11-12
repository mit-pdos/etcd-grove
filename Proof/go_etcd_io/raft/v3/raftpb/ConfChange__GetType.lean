/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/ConfChange__GetType.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__GetType

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

theorem raftpb.ConfChange.GetType.wp_proof :
    raftpb.ConfChange.GetType.spec (GF := GF) (hG := hG) := by
  constructor
  · intro p dq m
    wp_start as Hm
    iNamed Hm
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    ihave (⟨%Hp, %Hv⟩ | ⟨#Hp, %Hpn⟩) := cellRO_cases $$ cT
    · subst Hp
      wp_auto
      rw [show raftpb.ConfChangeType_ConfChangeAddNode = #m.type by rw [Hv]; rfl]
      wp_auto
      iapply HΦ
      iunfold ownConfChange
      iframe
      iexists uf
      isplitr
      · ipureintro; exact Hnn
      iframe cT cN cI Hcs Hpb
    · wp_if_destruct
      · exact absurd rfl Hpn
      · iapply HΦ
        iunfold ownConfChange
        iframe
        iexists uf
        isplitr
        · ipureintro; exact Hnn
        iframe cT cN cI Hcs Hpb
  · wp_start
    wp_auto
    rw [show raftpb.ConfChangeType_ConfChangeAddNode = #(W32 0) from rfl]
    wp_auto
    iapply HΦ; ipureintro; trivial

end proof

end EtcdGrove
end Perennial
