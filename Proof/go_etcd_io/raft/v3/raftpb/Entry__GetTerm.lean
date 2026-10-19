/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/Entry__GetTerm.lean`.
-/
module

public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm

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

theorem raftpb.Entry.GetTerm.wp_proof : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG) := by
  constructor
  · intro l dq e
    wp_start as He
    iNamed He
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    ihave (⟨%Hp, %Hv⟩ | ⟨#Hp, %Hpn⟩) := cellRO_cases $$ cT
    · subst Hp
      wp_auto
      rw [show (W64 0) = e.Term' from Hv.symm]
      iapply HΦ
      iunfold entPts
      iframe
      iexists uf
      isplitr
      · ipureintro; exact Hnn
      iframe cT cI cY Hd cS Hpb
    · wp_if_destruct
      · exact absurd rfl Hpn
      · iapply HΦ
        iunfold entPts
        iframe
        iexists uf
        isplitr
        · ipureintro; exact Hnn
        iframe cT cI cY Hd cS Hpb
  · wp_start
    wp_auto
    iapply HΦ; ipureintro; trivial

end proof

end EtcdGrove
end Perennial
