/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/ConfChangeSingle__GetNodeId.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.ConfChangeSingle__GetNodeId

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

theorem raftpb.ConfChangeSingle.GetNodeId.wp_proof :
    raftpb.ConfChangeSingle.GetNodeId.spec (GF := GF) (hG := hG) := by
  constructor
  · intro p dq c
    wp_start as Hm
    iNamed Hm
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    ihave (⟨%Hp, %Hv⟩ | ⟨#Hp, %Hpn⟩) := cellRO_cases $$ cN
    · subst Hp
      wp_auto
      rw [show (W64 0) = c.NodeId' from Hv.symm]
      iapply HΦ
      iunfold ccsPts
      iframe
      iexists uf
      isplitr
      · ipureintro; exact Hnn
      iframe cT cN Hpb
    · wp_if_destruct
      · exact absurd rfl Hpn
      · iapply HΦ
        iunfold ccsPts
        iframe
        iexists uf
        isplitr
        · ipureintro; exact Hnn
        iframe cT cN Hpb
  · wp_start
    wp_auto
    iapply HΦ; ipureintro; trivial

end proof

end EtcdGrove
end Perennial
