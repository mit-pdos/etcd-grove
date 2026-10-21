/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/ConfState__GetWitness.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetWitness

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

theorem raftpb.ConfState.GetWitness.wp_proof :
    raftpb.ConfState.GetWitness.spec (GF := GF) (hG := hG) := by
  intro p pw w dq Hnn
  wp_start as ⟨Hf, #cW⟩
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hnn
  ihave (⟨%Hq, %Hw⟩ | ⟨#Hq, %Hqn⟩) := cellRO_cases $$ cW
  · subst Hq Hw
    wp_auto
    rw [show (zero_val w64 : w64) = W64 0 from rfl]
    iapply HΦ
    iexact Hf
  · wp_if_destruct
    · exact absurd rfl Hqn
    · iapply HΦ
      iexact Hf

end proof

end EtcdGrove
end Perennial
