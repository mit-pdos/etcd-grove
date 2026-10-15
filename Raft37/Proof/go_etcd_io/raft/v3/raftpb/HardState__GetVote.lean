/-
Proof of `Raft37/Spec/go_etcd_io/raft/v3/raftpb/HardState__GetVote.lean`.
-/
module

public import Raft37.Spec.go_etcd_io.raft.v3.raftpb.HardState__GetVote

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

theorem raftpb.HardState.GetVote.wp_proof :
    raftpb.HardState.GetVote.spec (GF := GF) (hG := hG) := by
  constructor
  · intro p hs
    wp_start as Hh
    iNamed Hh
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    ihave (⟨%Hq, %Hv⟩ | ⟨#Hq, %Hqn⟩) := cellRO_cases $$ cV
    · subst Hq
      wp_auto
      rw [show (W64 0) = hs.Vote' from Hv.symm]
      iapply HΦ; ipureintro; trivial
    · wp_if_destruct
      · exact absurd rfl Hqn
      · iapply HΦ; ipureintro; trivial
  · wp_start
    wp_auto
    iapply HΦ; ipureintro; trivial

end proof

end EtcdGrove
end Perennial
