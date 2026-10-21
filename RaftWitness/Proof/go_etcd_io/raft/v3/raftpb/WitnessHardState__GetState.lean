/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/WitnessHardState__GetState.lean`.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.WitnessHardState__GetState

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

theorem raftpb.WitnessHardState.GetState.wp_proof :
    raftpb.WitnessHardState.GetState.spec (GF := GF) (hG := hG) := by
  constructor
  · intro p dq ps
    wp_start as ⟨%Hnn, Hf⟩
    wp_auto
    wp_if_destruct
    · exact absurd rfl Hnn
    · iapply HΦ; iexact Hf
  · wp_start
    wp_auto
    iapply HΦ; ipureintro; trivial

end proof

end EtcdGrove
end Perennial
